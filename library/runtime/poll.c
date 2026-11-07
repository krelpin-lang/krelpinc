/* Readiness polling for `std.net.Poller`: epoll on Linux, kqueue on macOS
 * and the BSDs.
 *
 * A `Poller` object holds a pointer to a `Poller` struct in its native
 * slot. Sockets are registered with an int token and the readiness they
 * care about. Polling is level-triggered: a socket that is still readable
 * is reported again by the next poll, so a handler doesn't have to drain
 * it. The events of the last poll are kept in the struct, merged so that
 * each token appears once, and read back one by one. */

#define _GNU_SOURCE

#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "krelpin.h"

#if defined(__linux__)
#define USE_EPOLL 1
#include <sys/epoll.h>
#elif defined(__APPLE__) || defined(__FreeBSD__) || defined(__NetBSD__) || defined(__OpenBSD__) || \
    defined(__DragonFly__)
#define USE_KQUEUE 1
#include <sys/event.h>
#include <sys/time.h>
#endif

/* The readiness bits `Poller.poll` decodes into an `Event`. */
enum {
    READY_READABLE = 1,
    READY_WRITABLE = 2,
    READY_CLOSED = 4,
    READY_ERROR = 8,
};

#define MAX_EVENTS 256

typedef struct {
    int32_t token;
    int32_t flags;
} Ready;

typedef struct {
    int fd;
    int32_t count;
    Ready ready[MAX_EVENTS];
} Poller;

static Poller *poller_of(void **slot) {
    return (Poller *)*slot;
}

/* Adds `flags` to the entry for `token`, or appends one. */
static void add_ready(Poller *poller, int32_t token, int32_t flags) {
    for (int32_t i = 0; i < poller->count; i++) {
        if (poller->ready[i].token == token) {
            poller->ready[i].flags |= flags;
            return;
        }
    }
    poller->ready[poller->count].token = token;
    poller->ready[poller->count].flags = flags;
    poller->count++;
}

void kr_poller_close(void *handle) {
    Poller *poller = handle;
    if (poller == NULL) {
        return;
    }
    if (poller->fd >= 0) {
        close(poller->fd);
    }
    kr_free(poller);
}

static bool in_range(int32_t index, const Poller *poller) {
    return index >= 0 && index < poller->count;
}

int32_t kr_poller_token(void **slot, int32_t index) {
    Poller *poller = poller_of(slot);
    return in_range(index, poller) ? poller->ready[index].token : -1;
}

int32_t kr_poller_flags(void **slot, int32_t index) {
    Poller *poller = poller_of(slot);
    return in_range(index, poller) ? poller->ready[index].flags : 0;
}

static bool adopt(void **slot, int fd) {
    if (fd < 0) {
        return kr_io_fail_errno();
    }
    int flags = fcntl(fd, F_GETFD);
    if (flags >= 0) {
        fcntl(fd, F_SETFD, flags | FD_CLOEXEC);
    }
    kr_poller_close(*slot);
    Poller *poller = kr_alloc((int64_t)sizeof(Poller));
    memset(poller, 0, sizeof *poller);
    poller->fd = fd;
    *slot = poller;
    return true;
}

#if defined(USE_EPOLL)

bool kr_poller_create(void **slot) {
    return adopt(slot, epoll_create1(EPOLL_CLOEXEC));
}

bool kr_net_register(void **slot, void *poller, int32_t token, bool readable, bool writable, bool again) {
    struct epoll_event event;
    memset(&event, 0, sizeof event);
    if (readable) {
        event.events |= EPOLLIN | EPOLLRDHUP;
    }
    if (writable) {
        event.events |= EPOLLOUT;
    }
    event.data.u64 = (uint32_t)token;
    int op = again ? EPOLL_CTL_MOD : EPOLL_CTL_ADD;
    if (epoll_ctl(((Poller *)poller)->fd, op, kr_net_fd(*slot), &event) != 0) {
        return kr_io_fail_errno();
    }
    return true;
}

bool kr_net_deregister(void **slot, void *poller) {
    struct epoll_event unused;
    if (epoll_ctl(((Poller *)poller)->fd, EPOLL_CTL_DEL, kr_net_fd(*slot), &unused) != 0) {
        return kr_io_fail_errno();
    }
    return true;
}

int32_t kr_poller_poll(void **slot, int64_t millis) {
    Poller *poller = poller_of(slot);
    poller->count = 0;
    struct epoll_event events[MAX_EVENTS];
    int timeout = millis < 0 ? -1 : millis > 2147483647 ? 2147483647 : (int)millis;
    int got = epoll_wait(poller->fd, events, MAX_EVENTS, timeout);
    if (got < 0) {
        if (errno == EINTR) {
            return 0;
        }
        kr_io_fail_errno();
        return -1;
    }
    for (int i = 0; i < got; i++) {
        uint32_t bits = events[i].events;
        int32_t flags = 0;
        if (bits & (EPOLLIN | EPOLLPRI | EPOLLRDHUP)) {
            flags |= READY_READABLE;
        }
        if (bits & EPOLLOUT) {
            flags |= READY_WRITABLE;
        }
        if (bits & (EPOLLHUP | EPOLLRDHUP)) {
            flags |= READY_CLOSED;
        }
        if (bits & EPOLLERR) {
            flags |= READY_ERROR;
        }
        add_ready(poller, (int32_t)(uint32_t)events[i].data.u64, flags);
    }
    return poller->count;
}

#elif defined(USE_KQUEUE)

bool kr_poller_create(void **slot) {
    return adopt(slot, kqueue());
}

/* Adds the filters asked for and deletes the others. With EV_RECEIPT
 * every change reports its own result, so deleting a filter that was never
 * added (ENOENT) doesn't hide a real failure. */
static bool change(void *poller, int fd, int32_t token, bool readable, bool writable, bool removing) {
    struct kevent changes[2];
    struct kevent results[2];
    void *udata = (void *)(intptr_t)token;
    bool read = !removing && readable;
    bool write = !removing && writable;
    EV_SET(&changes[0], fd, EVFILT_READ, (read ? EV_ADD : EV_DELETE) | EV_RECEIPT, 0, 0, udata);
    EV_SET(&changes[1], fd, EVFILT_WRITE, (write ? EV_ADD : EV_DELETE) | EV_RECEIPT, 0, 0, udata);
    int got;
    do {
        got = kevent(((Poller *)poller)->fd, changes, 2, results, 2, NULL);
    } while (got < 0 && errno == EINTR);
    if (got < 0) {
        return kr_io_fail_errno();
    }
    bool removed = false;
    for (int i = 0; i < got; i++) {
        int error = (int)results[i].data;
        if (!(results[i].flags & EV_ERROR) || error == 0) {
            removed |= removing;
            continue;
        }
        bool deleting = (results[i].filter == EVFILT_READ && !read) ||
                        (results[i].filter == EVFILT_WRITE && !write);
        if (deleting && error == ENOENT) {
            continue;
        }
        return kr_io_fail(error);
    }
    /* Like epoll, removing a socket that isn't registered fails. */
    if (removing && !removed) {
        return kr_io_fail(ENOENT);
    }
    return true;
}

bool kr_net_register(void **slot, void *poller, int32_t token, bool readable, bool writable, bool again) {
    (void)again;
    return change(poller, kr_net_fd(*slot), token, readable, writable, false);
}

bool kr_net_deregister(void **slot, void *poller) {
    return change(poller, kr_net_fd(*slot), 0, false, false, true);
}

int32_t kr_poller_poll(void **slot, int64_t millis) {
    Poller *poller = poller_of(slot);
    poller->count = 0;
    struct kevent events[MAX_EVENTS];
    struct timespec timeout;
    struct timespec *wait = NULL;
    if (millis >= 0) {
        timeout.tv_sec = (time_t)(millis / 1000);
        timeout.tv_nsec = (long)((millis % 1000) * 1000000);
        wait = &timeout;
    }
    int got = kevent(poller->fd, NULL, 0, events, MAX_EVENTS, wait);
    if (got < 0) {
        if (errno == EINTR) {
            return 0;
        }
        kr_io_fail_errno();
        return -1;
    }
    for (int i = 0; i < got; i++) {
        const struct kevent *event = &events[i];
        int32_t flags = 0;
        if (event->filter == EVFILT_READ) {
            flags |= READY_READABLE;
        } else if (event->filter == EVFILT_WRITE) {
            flags |= READY_WRITABLE;
        }
        if (event->flags & EV_EOF) {
            flags |= READY_CLOSED;
            /* A socket error, such as a refused connection, comes with EOF. */
            if (event->fflags != 0) {
                flags |= READY_ERROR;
            }
        }
        if (event->flags & EV_ERROR) {
            flags |= READY_ERROR;
        }
        add_ready(poller, (int32_t)(intptr_t)event->udata, flags);
    }
    return poller->count;
}

#else

bool kr_poller_create(void **slot) {
    (void)slot;
    return kr_io_fail(ENOSYS);
}

bool kr_net_register(void **slot, void *poller, int32_t token, bool readable, bool writable, bool again) {
    (void)slot, (void)poller, (void)token, (void)readable, (void)writable, (void)again;
    return kr_io_fail(ENOSYS);
}

bool kr_net_deregister(void **slot, void *poller) {
    (void)slot, (void)poller;
    return kr_io_fail(ENOSYS);
}

int32_t kr_poller_poll(void **slot, int64_t millis) {
    (void)slot, (void)millis;
    kr_io_fail(ENOSYS);
    return -1;
}

#endif
