#define _GNU_SOURCE

#include <dirent.h>
#include <netdb.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

#include "krelpin.h"

/* An errno value, or one of these for errors the C library doesn't name. */
enum {
    ERROR_NUL_IN_PATH = -1,
    ERROR_NOT_UTF8 = -2,
    ERROR_RESOLVE = -3,
    ERROR_BAD_ADDRESS = -4,
    ERROR_WOULD_BLOCK = -5,
};

static _Thread_local int last_error;
/* The `getaddrinfo` error behind ERROR_RESOLVE. */
static _Thread_local int resolve_error;

static bool failed(void) {
    last_error = errno != 0 ? errno : EIO;
    return false;
}

static bool failed_with(int error) {
    last_error = error;
    return false;
}

/* A NUL-terminated copy of a path, or NULL when the path contains a NUL
 * byte: the C library would silently cut it short there. */
static char *c_path(const KrString *path) {
    if (memchr(path->data, 0, (size_t)path->len) != NULL) {
        failed_with(ERROR_NUL_IN_PATH);
        return NULL;
    }
    char *copy = kr_alloc(path->len + 1);
    memcpy(copy, path->data, (size_t)path->len);
    copy[path->len] = 0;
    return copy;
}

/* Text read from a file must be UTF-8, like every string. */
static KrString *checked_text(const char *bytes, int64_t len) {
    if (!kr_utf8_valid(bytes, len)) {
        failed_with(ERROR_NOT_UTF8);
        return NULL;
    }
    return kr_string_new(bytes, len);
}

KrString *kr_io_last_error(void) {
    const char *message;
    switch (last_error) {
    case ERROR_NUL_IN_PATH:
        message = "the path contains a NUL character";
        break;
    case ERROR_NOT_UTF8:
        message = "the data is not valid UTF-8";
        break;
    case ERROR_RESOLVE:
        message = gai_strerror(resolve_error);
        break;
    case ERROR_WOULD_BLOCK:
        message = "the socket is non-blocking and isn't ready; wait for it with a `Poller`";
        break;
    case ERROR_BAD_ADDRESS:
        message = "expected an address like `127.0.0.1:8080`, `[::1]:8080` or `localhost:8080`";
        break;
    default:
        message = strerror(last_error);
        break;
    }
    return kr_string_new(message, (int64_t)strlen(message));
}

bool kr_io_fail(int error) {
    last_error = error != 0 ? error : EIO;
    return false;
}

bool kr_io_fail_errno(void) {
    return failed();
}

bool kr_io_fail_resolve(int error) {
    resolve_error = error;
    return failed_with(ERROR_RESOLVE);
}

bool kr_io_fail_bad_address(void) {
    return failed_with(ERROR_BAD_ADDRESS);
}

bool kr_io_fail_would_block(void) {
    return failed_with(ERROR_WOULD_BLOCK);
}

bool kr_io_fail_nul(void) {
    return failed_with(ERROR_NUL_IN_PATH);
}

bool kr_io_fail_not_utf8(void) {
    return failed_with(ERROR_NOT_UTF8);
}

void kr_io_clear_error(void) {
    last_error = 0;
}

bool kr_io_failed(void) {
    return last_error != 0;
}

KrString *kr_io_read_file(const KrString *path) {
    void *file = kr_file_open(path, 0);
    if (file == NULL) {
        return NULL;
    }
    KrString *text = kr_file_read_all(file);
    kr_file_close(file);
    return text;
}

bool kr_io_write_file(const KrString *path, const KrString *text, bool append) {
    void *file = kr_file_open(path, append ? 2 : 1);
    if (file == NULL) {
        return false;
    }
    bool written = kr_file_write(file, text);
    if (fclose(file) != 0 && written) {
        return failed();
    }
    return written;
}

static int status(const KrString *path, struct stat *info) {
    char *name = c_path(path);
    if (name == NULL) {
        return -1;
    }
    int result = stat(name, info);
    kr_free(name);
    return result;
}

bool kr_io_exists(const KrString *path) {
    struct stat info;
    return status(path, &info) == 0;
}

bool kr_io_is_file(const KrString *path) {
    struct stat info;
    return status(path, &info) == 0 && S_ISREG(info.st_mode);
}

bool kr_io_is_directory(const KrString *path) {
    struct stat info;
    return status(path, &info) == 0 && S_ISDIR(info.st_mode);
}

int64_t kr_io_size(const KrString *path) {
    struct stat info;
    errno = 0;
    if (status(path, &info) != 0) {
        failed();
        return -1;
    }
    return (int64_t)info.st_size;
}

bool kr_io_remove(const KrString *path) {
    char *name = c_path(path);
    if (name == NULL) {
        return false;
    }
    errno = 0;
    int result = remove(name);
    kr_free(name);
    return result == 0 || failed();
}

bool kr_io_create_directories(const KrString *path) {
    if (path->len == 0) {
        return failed_with(ENOENT);
    }
    char *name = c_path(path);
    if (name == NULL) {
        return false;
    }
    errno = 0;
    for (char *at = name + 1;; at++) {
        bool end = *at == 0;
        if (*at == '/' || end) {
            char saved = *at;
            *at = 0;
            if (mkdir(name, 0777) != 0 && errno != EEXIST) {
                kr_free(name);
                return failed();
            }
            *at = saved;
        }
        if (end) {
            break;
        }
    }
    struct stat info;
    bool directory = stat(name, &info) == 0 && S_ISDIR(info.st_mode);
    kr_free(name);
    if (!directory) {
        errno = ENOTDIR;
        return failed();
    }
    return true;
}

static int compare_names(const void *a, const void *b) {
    return strcmp(*(char *const *)a, *(char *const *)b);
}

KrArray *kr_io_list(const KrString *path, const KrType *array_type) {
    char *name = c_path(path);
    if (name == NULL) {
        return NULL;
    }
    errno = 0;
    DIR *dir = opendir(name);
    kr_free(name);
    if (dir == NULL) {
        failed();
        return NULL;
    }
    int64_t count = 0;
    int64_t cap = 16;
    char **names = kr_alloc(cap * (int64_t)sizeof(char *));
    struct dirent *entry;
    while ((entry = readdir(dir)) != NULL) {
        if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) {
            continue;
        }
        if (count == cap) {
            cap *= 2;
            names = kr_realloc(names, cap * (int64_t)sizeof(char *));
        }
        size_t len = strlen(entry->d_name);
        names[count] = kr_alloc((int64_t)len + 1);
        memcpy(names[count], entry->d_name, len + 1);
        count++;
    }
    closedir(dir);
    qsort(names, (size_t)count, sizeof(char *), compare_names);
    KrArray *array = kr_alloc((int64_t)sizeof(KrArray) + count * (int64_t)sizeof(void *));
    array->type = array_type;
    array->len = count;
    KrString **out = (KrString **)array->data;
    for (int64_t i = 0; i < count; i++) {
        out[i] = kr_string_from_lossy(names[i], (int64_t)strlen(names[i]));
        kr_free(names[i]);
    }
    kr_free(names);
    return array;
}

void *kr_file_open(const KrString *path, int32_t mode) {
    char *name = c_path(path);
    if (name == NULL) {
        return NULL;
    }
    const char *flags = mode == 0 ? "rb" : (mode == 1 ? "wb" : "ab");
    errno = 0;
    FILE *file = fopen(name, flags);
    kr_free(name);
    if (file == NULL) {
        failed();
    }
    return file;
}

bool kr_file_write(void *file, const KrString *text) {
    errno = 0;
    if (fwrite(text->data, 1, (size_t)text->len, file) != (size_t)text->len) {
        return failed();
    }
    return true;
}

bool kr_file_write_bytes(void *file, const KrArray *bytes) {
    errno = 0;
    if (bytes->len > 0 && fwrite(bytes->data, 1, (size_t)bytes->len, file) != (size_t)bytes->len) {
        return failed();
    }
    return true;
}

KrArray *kr_file_read_bytes(void *file, int32_t max, const KrType *array_type) {
    KrArray *array = kr_alloc((int64_t)sizeof(KrArray) + max);
    array->type = array_type;
    errno = 0;
    last_error = 0;
    size_t got = fread(array->data, 1, (size_t)max, file);
    if (got == 0 && ferror(file)) {
        kr_free(array);
        failed();
        return NULL;
    }
    array->len = (int64_t)got;
    return array;
}

bool kr_file_flush(void *file) {
    errno = 0;
    return fflush(file) == 0 || failed();
}

KrString *kr_file_read_line(void *file) {
    char *line = NULL;
    size_t cap = 0;
    errno = 0;
    last_error = 0;
    ssize_t len = getline(&line, &cap, file);
    if (len < 0) {
        free(line);
        if (ferror(file)) {
            failed();
        }
        return NULL;
    }
    if (len > 0 && line[len - 1] == '\n') {
        len--;
        if (len > 0 && line[len - 1] == '\r') {
            len--;
        }
    }
    KrString *text = checked_text(line, len);
    free(line);
    return text;
}

KrString *kr_file_read_all(void *file) {
    int64_t cap = 4096;
    int64_t len = 0;
    char *buffer = kr_alloc(cap);
    errno = 0;
    for (;;) {
        if (len == cap) {
            cap *= 2;
            buffer = kr_realloc(buffer, cap);
        }
        size_t read = fread(buffer + len, 1, (size_t)(cap - len), file);
        len += (int64_t)read;
        if (read == 0) {
            break;
        }
    }
    if (ferror(file)) {
        kr_free(buffer);
        failed();
        return NULL;
    }
    KrString *text = checked_text(buffer, len);
    kr_free(buffer);
    return text;
}

void kr_file_close(void *file) {
    if (file != NULL) {
        fclose(file);
    }
}

void kr_console_eprint(const KrString *string) {
    fflush(stdout);
    fwrite(string->data, 1, (size_t)string->len, stderr);
}

void kr_system_exit(int32_t code) {
    kr_runtime_exit();
    fflush(stdout);
    fflush(stderr);
    exit(code);
}

KrString *kr_system_env(const KrString *name) {
    char *key = c_path(name);
    if (key == NULL) {
        return NULL;
    }
    const char *value = getenv(key);
    kr_free(key);
    if (value == NULL) {
        return NULL;
    }
    return kr_string_from_lossy(value, (int64_t)strlen(value));
}

KrString *kr_io_canonical_path(const KrString *path) {
    char *name = c_path(path);
    if (name == NULL) {
        return NULL;
    }
    errno = 0;
    char *resolved = realpath(name, NULL);
    kr_free(name);
    if (resolved == NULL) {
        failed();
        return NULL;
    }
    KrString *result = kr_string_from_lossy(resolved, (int64_t)strlen(resolved));
    free(resolved);
    return result;
}

KrString *kr_system_working_directory(void) {
    char *cwd = getcwd(NULL, 0);
    if (cwd == NULL) {
        return kr_string_new(".", 1);
    }
    KrString *result = kr_string_from_lossy(cwd, (int64_t)strlen(cwd));
    free(cwd);
    return result;
}

int64_t kr_system_millis(void) {
    struct timespec now;
    clock_gettime(CLOCK_REALTIME, &now);
    return (int64_t)now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

int64_t kr_system_epoch_nanos(void) {
    struct timespec now;
    clock_gettime(CLOCK_REALTIME, &now);
    return (int64_t)now.tv_sec * 1000000000 + now.tv_nsec;
}

int64_t kr_system_nanos(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (int64_t)now.tv_sec * 1000000000 + now.tv_nsec;
}

bool kr_io_is_symlink(const KrString *path) {
    char *name = c_path(path);
    if (name == NULL) {
        return false;
    }
    struct stat info;
    int result = lstat(name, &info);
    kr_free(name);
    return result == 0 && S_ISLNK(info.st_mode);
}

bool kr_io_create_directory(const KrString *path) {
    char *name = c_path(path);
    if (name == NULL) {
        return false;
    }
    errno = 0;
    int result = mkdir(name, 0777);
    kr_free(name);
    return result == 0 || failed();
}

bool kr_io_rename(const KrString *from, const KrString *to) {
    char *source = c_path(from);
    if (source == NULL) {
        return false;
    }
    char *target = c_path(to);
    if (target == NULL) {
        kr_free(source);
        return false;
    }
    errno = 0;
    int result = rename(source, target);
    kr_free(source);
    kr_free(target);
    return result == 0 || failed();
}

static FILE *open_raw(const KrString *path, const char *mode) {
    char *name = c_path(path);
    if (name == NULL) {
        return NULL;
    }
    errno = 0;
    FILE *file = fopen(name, mode);
    kr_free(name);
    if (file == NULL) {
        failed();
    }
    return file;
}

bool kr_io_copy(const KrString *from, const KrString *to) {
    FILE *source = open_raw(from, "rb");
    if (source == NULL) {
        return false;
    }
    FILE *target = open_raw(to, "wb");
    if (target == NULL) {
        fclose(source);
        return false;
    }
    char buffer[65536];
    bool ok = true;
    errno = 0;
    for (;;) {
        size_t count = fread(buffer, 1, sizeof buffer, source);
        if (count > 0 && fwrite(buffer, 1, count, target) != count) {
            ok = failed();
            break;
        }
        if (count < sizeof buffer) {
            if (ferror(source)) {
                ok = failed();
            }
            break;
        }
    }
    fclose(source);
    if (fclose(target) != 0 && ok) {
        ok = failed();
    }
    return ok;
}

KrArray *kr_io_read_bytes(const KrString *path, const KrType *array_type) {
    FILE *file = open_raw(path, "rb");
    if (file == NULL) {
        return NULL;
    }
    int64_t cap = 4096;
    int64_t len = 0;
    char *data = kr_alloc(cap);
    errno = 0;
    for (;;) {
        if (len == cap) {
            cap *= 2;
            data = kr_realloc(data, cap);
        }
        size_t count = fread(data + len, 1, (size_t)(cap - len), file);
        len += (int64_t)count;
        if (count == 0) {
            break;
        }
    }
    bool error = ferror(file) != 0;
    fclose(file);
    if (error) {
        kr_free(data);
        failed();
        return NULL;
    }
    KrArray *array = kr_alloc((int64_t)sizeof(KrArray) + len);
    array->type = array_type;
    array->len = len;
    if (len > 0) {
        memcpy(array->data, data, (size_t)len);
    }
    kr_free(data);
    return array;
}

bool kr_io_write_bytes(const KrString *path, const KrArray *bytes, bool append) {
    FILE *file = open_raw(path, append ? "ab" : "wb");
    if (file == NULL) {
        return false;
    }
    errno = 0;
    bool ok = bytes->len == 0 || fwrite(bytes->data, 1, (size_t)bytes->len, file) == (size_t)bytes->len;
    if (!ok) {
        failed();
    }
    if (fclose(file) != 0 && ok) {
        ok = failed();
    }
    return ok;
}

KrString *kr_system_os_name(void) {
#if defined(__APPLE__)
    const char *name = "macos";
#elif defined(__linux__)
    const char *name = "linux";
#elif defined(_WIN32)
    const char *name = "windows";
#elif defined(__FreeBSD__)
    const char *name = "freebsd";
#else
    const char *name = "unknown";
#endif
    return kr_string_new(name, (int64_t)strlen(name));
}
