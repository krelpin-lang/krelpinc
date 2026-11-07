#define _GNU_SOURCE

#include <pthread.h>
#include <sched.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "krelpin.h"

#if defined(__APPLE__)
#include <stdlib.h>
#elif defined(__linux__)
#include <errno.h>
#include <sys/random.h>
#endif

static int saved_argc;
static char **saved_argv;
static pthread_mutex_t console_lock = PTHREAD_MUTEX_INITIALIZER;

void kr_runtime_init(int argc, char **argv) {
    saved_argc = argc;
    saved_argv = argv;
}

void kr_runtime_exit(void) {
    fflush(stdout);
}

KrArray *kr_runtime_args(const KrType *array_type) {
    int64_t count = saved_argc > 1 ? saved_argc - 1 : 0;
    KrArray *array = kr_alloc((int64_t)sizeof(KrArray) + count * (int64_t)sizeof(void *));
    array->type = array_type;
    array->len = count;
    KrString **out = (KrString **)array->data;
    for (int64_t i = 0; i < count; i++) {
        out[i] = kr_string_from_lossy(saved_argv[i + 1], (int64_t)strlen(saved_argv[i + 1]));
    }
    return array;
}

void kr_console_print(const KrString *string) {
    pthread_mutex_lock(&console_lock);
    fwrite(string->data, 1, (size_t)string->len, stdout);
    pthread_mutex_unlock(&console_lock);
}

void kr_console_newline(void) {
    pthread_mutex_lock(&console_lock);
    fputc('\n', stdout);
    pthread_mutex_unlock(&console_lock);
}

KrString *kr_console_read_line(void) {
    fflush(stdout);
    char *line = NULL;
    size_t cap = 0;
    ssize_t len = getline(&line, &cap, stdin);
    if (len < 0) {
        free(line);
        return NULL;
    }
    while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r')) {
        len--;
    }
    KrString *string = kr_string_from_lossy(line, len);
    free(line);
    return string;
}

bool (*kr_uncaught_hook)(const KrType *type, const KrString *message);

void kr_uncaught(const KrType *type, const KrString *message) {
    fflush(stdout);
    if (kr_uncaught_hook != NULL && kr_uncaught_hook(type, message)) {
        return;
    }
    if (message == NULL) {
        fprintf(stderr, "Exception in thread \"main\" %s\n", type->name);
    } else {
        fprintf(stderr, "Exception in thread \"main\" %s: %.*s\n", type->name,
                (int)message->len, message->data);
    }
}

void kr_report_thread(const KrType *type, const KrString *message) {
    fflush(stdout);
    if (message == NULL) {
        fprintf(stderr, "Exception in a spawned thread: %s\n", type->name);
    } else {
        fprintf(stderr, "Exception in a spawned thread: %s: %.*s\n", type->name, (int)message->len,
                message->data);
    }
}

static _Thread_local uint64_t random_state;

double kr_random(void) {
    if (random_state == 0) {
        struct timespec now;
        clock_gettime(CLOCK_REALTIME, &now);
        random_state = ((uint64_t)now.tv_nsec << 20) ^ (uint64_t)now.tv_sec ^
                       (uint64_t)(uintptr_t)&random_state;
        random_state |= 1;
    }
    random_state ^= random_state >> 12;
    random_state ^= random_state << 25;
    random_state ^= random_state >> 27;
    uint64_t bits = random_state * 2685821657736338717ULL;
    return (double)(bits >> 11) * (1.0 / 9007199254740992.0);
}

typedef struct {
    void (*entry)(void *);
    void *argument;
} ThreadStart;

static void *run_thread(void *pointer) {
    ThreadStart start = *(ThreadStart *)pointer;
    kr_free(pointer);
    kr_stack_guard_thread_start();
    start.entry(start.argument);
    kr_stack_guard_thread_end();
    return NULL;
}

void *kr_thread_spawn(void (*entry)(void *), void *argument) {
    ThreadStart *start = kr_alloc(sizeof(ThreadStart));
    start->entry = entry;
    start->argument = argument;
    pthread_t *thread = kr_alloc(sizeof(pthread_t));
    if (pthread_create(thread, NULL, run_thread, start) != 0) {
        kr_panic("failed to spawn a thread");
    }
    return thread;
}

void kr_thread_join(void *handle) {
    if (handle == NULL) {
        return;
    }
    pthread_join(*(pthread_t *)handle, NULL);
    kr_free(handle);
}

void kr_thread_sleep(int64_t millis) {
    if (millis <= 0) {
        return;
    }
    struct timespec duration = {millis / 1000, (millis % 1000) * 1000000};
    while (nanosleep(&duration, &duration) != 0) {
    }
}

typedef struct {
    pthread_mutex_t mutex;
    pthread_cond_t ready;
} KrMonitor;

void *kr_mutex_new(void) {
    KrMonitor *monitor = kr_alloc(sizeof(KrMonitor));
    pthread_mutex_init(&monitor->mutex, NULL);
    pthread_cond_init(&monitor->ready, NULL);
    return monitor;
}

void kr_mutex_lock(void *monitor) {
    pthread_mutex_lock(&((KrMonitor *)monitor)->mutex);
}

void kr_mutex_unlock(void *monitor) {
    pthread_mutex_unlock(&((KrMonitor *)monitor)->mutex);
}

void kr_mutex_wait(void *handle) {
    KrMonitor *monitor = handle;
    pthread_cond_wait(&monitor->ready, &monitor->mutex);
}

bool kr_mutex_wait_millis(void *handle, int64_t millis) {
    KrMonitor *monitor = handle;
    if (millis < 0) {
        millis = 0;
    }
    struct timespec deadline;
    clock_gettime(CLOCK_REALTIME, &deadline);
    deadline.tv_sec += millis / 1000;
    deadline.tv_nsec += (millis % 1000) * 1000000;
    if (deadline.tv_nsec >= 1000000000) {
        deadline.tv_sec += 1;
        deadline.tv_nsec -= 1000000000;
    }
    return pthread_cond_timedwait(&monitor->ready, &monitor->mutex, &deadline) == 0;
}

void kr_mutex_notify(void *handle) {
    pthread_cond_signal(&((KrMonitor *)handle)->ready);
}

void kr_mutex_notify_all(void *handle) {
    pthread_cond_broadcast(&((KrMonitor *)handle)->ready);
}

void kr_mutex_free(void *handle) {
    if (handle == NULL) {
        return;
    }
    KrMonitor *monitor = handle;
    pthread_cond_destroy(&monitor->ready);
    pthread_mutex_destroy(&monitor->mutex);
    kr_free(monitor);
}

void *kr_rwlock_new(void) {
    pthread_rwlock_t *lock = kr_alloc(sizeof(pthread_rwlock_t));
    pthread_rwlock_init(lock, NULL);
    return lock;
}

void kr_rwlock_read(void *lock) {
    pthread_rwlock_rdlock(lock);
}

void kr_rwlock_write(void *lock) {
    pthread_rwlock_wrlock(lock);
}

void kr_rwlock_unlock(void *lock) {
    pthread_rwlock_unlock(lock);
}

void kr_rwlock_free(void *lock) {
    if (lock == NULL) {
        return;
    }
    pthread_rwlock_destroy(lock);
    kr_free(lock);
}

static int64_t tests_total;
static int64_t tests_failed;
static int64_t tests_passed;
static char *failures;
static size_t failures_len;

void kr_test_begin(int64_t count) {
    tests_total = count;
    printf("\nrunning %lld test%s\n", (long long)count, count == 1 ? "" : "s");
}

void kr_test_passed(const char *name) {
    tests_passed++;
    printf("test %s ... ok\n", name);
}

void kr_test_failed(const char *name, const KrType *type, const KrString *message) {
    tests_failed++;
    printf("test %s ... FAILED\n", name);
    char line[1024];
    int len;
    if (message == NULL) {
        len = snprintf(line, sizeof line, "    %s: %s\n", name, type->name);
    } else {
        len = snprintf(line, sizeof line, "    %s: %s: %.*s\n", name, type->name,
                       (int)message->len, message->data);
    }
    if (len < 0) {
        return;
    }
    size_t size = (size_t)len < sizeof line ? (size_t)len : sizeof line - 1;
    failures = kr_realloc(failures, (int64_t)(failures_len + size + 1));
    memcpy(failures + failures_len, line, size);
    failures_len += size;
    failures[failures_len] = '\0';
}

int32_t kr_test_end(void) {
    if (tests_failed > 0) {
        printf("\nfailures:\n%s", failures);
    }
    printf("\ntest result: %s. %lld passed; %lld failed\n\n", tests_failed > 0 ? "FAILED" : "ok",
           (long long)tests_passed, (long long)tests_failed);
    kr_free(failures);
    failures = NULL;
    return tests_failed > 0 ? 101 : 0;
}

void kr_export_failed(const KrType *type, const KrString *message) {
    kr_uncaught(type, message);
    abort();
}

void kr_once(_Atomic int32_t *state, void (*init)(void)) {
    int32_t expected = 0;
    if (atomic_compare_exchange_strong(state, &expected, 1)) {
        init();
        atomic_store(state, 2);
        return;
    }
    while (atomic_load(state) != 2) {
        sched_yield();
    }
}

void kr_secure_random_fill(KrArray *bytes) {
#if defined(__APPLE__)
    arc4random_buf(bytes->data, (size_t)bytes->len);
#elif defined(__linux__)
    size_t done = 0;
    while (done < (size_t)bytes->len) {
        ssize_t got = getrandom(bytes->data + done, (size_t)bytes->len - done, 0);
        if (got < 0) {
            if (errno == EINTR) {
                continue;
            }
            fprintf(stderr, "fatal: the operating system has no secure random source\n");
            abort();
        }
        done += (size_t)got;
    }
#else
#error "no secure random source for this platform"
#endif
}
