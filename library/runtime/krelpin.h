#ifndef KRELPIN_H
#define KRELPIN_H

#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct KrType KrType;

struct KrType {
    const char *name;
    const KrType *super;
    void (*drop)(void *object);
    int64_t size;
    const KrType *const *interfaces;
    int64_t kind;
    int64_t vtable_len;
    void *vtable[];
};

enum {
    KR_KIND_CLASS = 0,
    KR_KIND_STRING = 1,
    KR_KIND_ARRAY = 2,
    KR_KIND_BOX = 3,
    KR_KIND_CLOSURE = 4,
    KR_KIND_INTERFACE = 5,
};

typedef struct {
    const KrType *type;
} KrObject;

typedef struct {
    const KrType *type;
    _Atomic int64_t refs;
    int64_t len;
    int64_t chars;
    char data[];
} KrString;

typedef struct {
    const KrType *type;
    int64_t len;
    _Alignas(16) unsigned char data[];
} KrArray;

typedef struct {
    char *data;
    int64_t len;
    int64_t cap;
    int64_t chars;
} KrBuilder;

typedef struct {
    int32_t (*hash)(const void *key);
    bool (*eq)(const void *a, const void *b);
    void (*drop_key)(void *key);
    void (*drop_value)(void *value);
    int64_t entry_size;
    int64_t key_offset;
    int64_t value_offset;
    int64_t value_size;
} KrTableShape;

typedef struct {
    unsigned char *entries;
    int64_t entry_count;
    int64_t entry_cap;
    int64_t live;
    int64_t *index;
    int64_t index_cap;
} KrTable;

extern const KrType kr_string_type;
extern _Thread_local void *kr_pending;
extern bool (*kr_uncaught_hook)(const KrType *type, const KrString *message);

void *kr_alloc(int64_t size);
void *kr_realloc(void *pointer, int64_t size);
void kr_free(void *pointer);
void *kr_new_object(const KrType *type);
void kr_drop_object(void *object);
bool kr_instance_of(const void *object, const KrType *target);
_Noreturn void kr_panic(const char *message);

KrString *kr_string_new(const char *bytes, int64_t len);
KrString *kr_string_from_lossy(const char *bytes, int64_t len);
bool kr_utf8_valid(const char *bytes, int64_t len);

/* Sockets for `std.net`; see net.c. */
void kr_net_close(void *handle);
KrString *kr_net_local_addr(void **slot);
bool kr_net_set_timeout(void **slot, int64_t millis, bool writing);
bool kr_net_set_nonblocking(void **slot, bool on);
int kr_net_fd(void *handle);
bool kr_net_register(void **slot, void *poller, int32_t token, bool readable, bool writable, bool again);
bool kr_net_deregister(void **slot, void *poller);
bool kr_tcp_listener_bind(void **slot, const KrString *address);
bool kr_tcp_stream_connect(void **slot, const KrString *address);
bool kr_tcp_stream_accept(void **slot, void *listener);
int32_t kr_tcp_stream_try_accept(void **slot, void *listener);
bool kr_tcp_stream_start_connect(void **slot, const KrString *address);
int32_t kr_tcp_stream_finish_connect(void **slot);
KrString *kr_tcp_stream_peer_addr(void **slot);
bool kr_tcp_stream_set_no_delay(void **slot, bool on);
KrString *kr_tcp_stream_read_line(void **slot);
KrString *kr_tcp_stream_try_read_line(void **slot);
bool kr_tcp_stream_at_end(void **slot);
KrString *kr_tcp_stream_read_all(void **slot);
KrArray *kr_tcp_stream_read(void **slot, int32_t max, const KrType *array_type);
KrArray *kr_tcp_stream_try_read(void **slot, int32_t max, const KrType *array_type);
bool kr_tcp_stream_write(void **slot, const KrString *text);
bool kr_tcp_stream_write_bytes(void **slot, const KrArray *bytes);
int32_t kr_tcp_stream_try_write(void **slot, const KrArray *bytes, int32_t offset);
void kr_tcp_stream_queue_text(void **slot, const KrString *text);
void kr_tcp_stream_queue_bytes(void **slot, const KrArray *bytes);
int32_t kr_tcp_stream_flush(void **slot);
int64_t kr_tcp_stream_queued(void **slot);
bool kr_tcp_stream_shutdown_write(void **slot);
bool kr_udp_bind(void **slot, const KrString *address);
bool kr_udp_send_to(void **slot, const KrArray *bytes, const KrString *address);
int32_t kr_udp_try_send_to(void **slot, const KrArray *bytes, const KrString *address);
KrArray *kr_udp_receive(void **slot, int32_t max, const KrType *array_type);
KrArray *kr_udp_try_receive(void **slot, int32_t max, const KrType *array_type);
KrString *kr_udp_last_sender(void **slot);
KrArray *kr_string_bytes(const KrString *string, const KrType *array_type);
KrString *kr_string_from_utf8(const KrArray *bytes);

/* Readiness polling for non-blocking sockets; see poll.c. */
bool kr_poller_create(void **slot);
void kr_poller_close(void *handle);
int32_t kr_poller_poll(void **slot, int64_t millis);
int32_t kr_poller_token(void **slot, int32_t index);
int32_t kr_poller_flags(void **slot, int32_t index);

/* The error that `Files.lastError` describes, shared by files and sockets.
 * Each `kr_io_fail*` records an error and returns false. */
bool kr_io_fail(int error);
bool kr_io_fail_errno(void);
bool kr_io_fail_resolve(int error);
bool kr_io_fail_bad_address(void);
bool kr_io_fail_not_utf8(void);
bool kr_io_fail_nul(void);
bool kr_io_fail_would_block(void);
void kr_io_clear_error(void);

/* `strtod` and `snprintf` in the "C" locale, whatever the host has set. */
double kr_c_strtod(const char *text, char **end);
int kr_c_snprintf(char *buffer, size_t size, const char *format, ...)
    __attribute__((format(printf, 3, 4)));
void kr_string_retain(KrString *string);
void kr_string_release(void *string);
KrString *kr_string_concat(const KrString *a, const KrString *b);
int32_t kr_string_length(const KrString *string);
int64_t kr_string_byte_offset(const KrString *string, int64_t chars);
KrArray *kr_string_chars(const KrString *string, const KrType *array_type);
KrString *kr_string_substring(const KrString *string, int32_t begin, int32_t end);
int32_t kr_string_index_of(const KrString *string, const KrString *text);
bool kr_string_starts_with(const KrString *string, const KrString *prefix);
bool kr_string_ends_with(const KrString *string, const KrString *suffix);
KrString *kr_string_to_upper(const KrString *string);
KrString *kr_string_to_lower(const KrString *string);
KrString *kr_string_trim(const KrString *string);
KrString *kr_string_trim_start(const KrString *string);
KrString *kr_string_trim_end(const KrString *string);
int32_t kr_string_char_at(const KrString *string, int32_t index);
int32_t kr_string_index_of_from(const KrString *string, const KrString *text, int32_t from);
int32_t kr_string_last_index_of(const KrString *string, const KrString *text);
KrString *kr_string_replace(const KrString *string, const KrString *target,
                            const KrString *replacement);
KrString *kr_string_repeat(const KrString *string, int32_t count);
KrArray *kr_string_split(const KrString *string, const KrString *separator,
                         const KrType *array_type);
int32_t kr_string_compare(const KrString *a, const KrString *b);
bool kr_string_equals(const KrString *a, const KrString *b);
int32_t kr_string_hash(const KrString *string);
KrString *kr_string_join(const KrString *separator, const KrArray *parts);
KrString *kr_string_from_long(int64_t value);
KrString *kr_string_from_double(double value);
KrString *kr_string_from_float(float value);
KrString *kr_string_from_char(int32_t value);
KrString *kr_string_from_bool(bool value);
KrString *kr_string_describe(const void *object);
KrString *kr_string_bounds(int64_t index, int64_t len);
KrString *kr_string_cast(const void *object, const KrString *target);
KrString *kr_string_number_format(const KrString *text);
bool kr_parse_long(const KrString *text, int64_t min, int64_t max, int64_t *out);
bool kr_parse_double(const KrString *text, double *out);
KrString *kr_format_long(int64_t value, const KrString *spec);
KrString *kr_format_double(double value, const KrString *spec);
KrString *kr_format_text(const KrString *value, const KrString *spec);

void kr_console_print(const KrString *string);
void kr_console_newline(void);
KrString *kr_console_read_line(void);
void kr_uncaught(const KrType *type, const KrString *message);
void kr_report_thread(const KrType *type, const KrString *message);
void kr_test_begin(int64_t count);
void kr_test_passed(const char *name);
void kr_test_failed(const char *name, const KrType *type, const KrString *message);
int32_t kr_test_end(void);
void kr_export_failed(const KrType *type, const KrString *message);
void kr_once(_Atomic int32_t *state, void (*init)(void));

bool kr_char_is_digit(int32_t c);
bool kr_char_is_letter(int32_t c);
bool kr_char_is_whitespace(int32_t c);
bool kr_char_is_upper(int32_t c);
bool kr_char_is_lower(int32_t c);
int32_t kr_char_to_upper(int32_t c);
int32_t kr_char_to_lower(int32_t c);
int32_t kr_char_to_upper_full(int32_t c, int32_t out[3]);
int32_t kr_char_to_lower_full(int32_t c, int32_t out[3]);

double kr_random(void);

void *kr_thread_spawn(void (*entry)(void *), void *argument);
void kr_thread_join(void *handle);
void kr_thread_sleep(int64_t millis);
void *kr_mutex_new(void);
void kr_mutex_lock(void *mutex);
void kr_mutex_unlock(void *mutex);
void kr_mutex_wait(void *mutex);
bool kr_mutex_wait_millis(void *mutex, int64_t millis);
void kr_mutex_notify(void *mutex);
void kr_mutex_notify_all(void *mutex);
void kr_secure_random_fill(KrArray *bytes);
void *kr_rwlock_new(void);
void kr_rwlock_read(void *lock);
void kr_rwlock_write(void *lock);
void kr_rwlock_unlock(void *lock);
void kr_rwlock_free(void *lock);
void kr_mutex_free(void *mutex);

void kr_table_init(KrTable *table);
void kr_table_free(KrTable *table, const KrTableShape *shape);
void kr_table_clear(KrTable *table, const KrTableShape *shape);
void *kr_table_find(KrTable *table, const KrTableShape *shape, const void *key);
void *kr_table_insert(KrTable *table, const KrTableShape *shape, void *entry, bool *existed);
bool kr_table_remove(KrTable *table, const KrTableShape *shape, const void *key, void *out);
int64_t kr_table_slot_count(const KrTable *table);
void *kr_table_slot(const KrTable *table, const KrTableShape *shape, int64_t index);

void kr_builder_append(KrBuilder *builder, const KrString *text);
bool kr_builder_insert(KrBuilder *builder, int32_t index, const KrString *text);
bool kr_builder_truncate(KrBuilder *builder, int32_t length);
void kr_builder_reverse(KrBuilder *builder);
KrString *kr_builder_to_string(const KrBuilder *builder);
int32_t kr_builder_length(const KrBuilder *builder);
void kr_builder_clear(KrBuilder *builder);
void kr_builder_free(KrBuilder *builder);

KrString *kr_io_last_error(void);
bool kr_io_failed(void);
KrString *kr_io_read_file(const KrString *path);
bool kr_io_write_file(const KrString *path, const KrString *text, bool append);
bool kr_io_exists(const KrString *path);
bool kr_io_is_file(const KrString *path);
bool kr_io_is_directory(const KrString *path);
int64_t kr_io_size(const KrString *path);
bool kr_io_remove(const KrString *path);
bool kr_io_create_directories(const KrString *path);
KrArray *kr_io_list(const KrString *path, const KrType *array_type);
bool kr_io_is_symlink(const KrString *path);
bool kr_io_create_directory(const KrString *path);
bool kr_io_rename(const KrString *from, const KrString *to);
bool kr_io_copy(const KrString *from, const KrString *to);
KrArray *kr_io_read_bytes(const KrString *path, const KrType *array_type);
bool kr_io_write_bytes(const KrString *path, const KrArray *bytes, bool append);
KrString *kr_system_os_name(void);
void *kr_file_open(const KrString *path, int32_t mode);
bool kr_file_write(void *file, const KrString *text);
bool kr_file_flush(void *file);
bool kr_file_write_bytes(void *file, const KrArray *bytes);
KrArray *kr_file_read_bytes(void *file, int32_t max, const KrType *array_type);
KrString *kr_file_read_line(void *file);
KrString *kr_file_read_all(void *file);
void kr_file_close(void *file);
void kr_console_eprint(const KrString *string);
_Noreturn void kr_system_exit(int32_t code);
KrString *kr_system_env(const KrString *name);
KrString *kr_system_working_directory(void);
KrString *kr_io_canonical_path(const KrString *path);

/* process.c: running other programs. */
int32_t kr_process_run(const KrArray *argv, const KrString *directory, const KrArray *env,
                       bool capture);
KrString *kr_process_captured(bool error);
int64_t kr_system_millis(void);
int64_t kr_system_nanos(void);
int64_t kr_system_epoch_nanos(void);

void kr_bridge_open(void);
KrString *kr_bridge_receive(void);
void kr_bridge_send(const KrString *line);
KrString *kr_bridge_escape(const KrString *text);
KrString *kr_bridge_unescape(const KrString *text);

void kr_runtime_init(int argc, char **argv);
void kr_stack_guard_install(void);
void kr_stack_guard_thread_start(void);
void kr_stack_guard_thread_end(void);
void kr_runtime_exit(void);
KrArray *kr_runtime_args(const KrType *array_type);

#endif
