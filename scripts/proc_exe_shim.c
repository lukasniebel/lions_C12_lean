#define _GNU_SOURCE

#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

/*
 * Lean discovers its installation by calling readlink on /proc/<pid>/exe.
 * Where procfs is not mounted that call fails, and only then do the launch
 * wrappers supply that one answer explicitly (LEAN_FAKE_APP_PATH).  Where the
 * call succeeds its result is returned unchanged, as is every other readlink
 * call, so the library has no effect on a system with procfs.
 */

typedef ssize_t (*readlink_fn)(const char *, char *, size_t);

static int is_current_process_exe(const char *path) {
  char proc_pid_exe[64];
  int written;

  if (path == NULL) {
    return 0;
  }
  if (strcmp(path, "/proc/self/exe") == 0 ||
      strcmp(path, "/proc/thread-self/exe") == 0) {
    return 1;
  }

  written = snprintf(proc_pid_exe, sizeof(proc_pid_exe), "/proc/%ld/exe",
                     (long)getpid());
  return written > 0 && (size_t)written < sizeof(proc_pid_exe) &&
         strcmp(path, proc_pid_exe) == 0;
}

static ssize_t copy_fake_app_path(char *buf, size_t bufsiz) {
  const char *fake_app_path = getenv("LEAN_FAKE_APP_PATH");
  size_t path_len;
  size_t copy_len;

  if (fake_app_path == NULL || fake_app_path[0] == '\0') {
    return -2;
  }
  if (buf == NULL) {
    errno = EFAULT;
    return -1;
  }
  if (bufsiz == 0) {
    errno = EINVAL;
    return -1;
  }

  path_len = strlen(fake_app_path);
  copy_len = path_len < bufsiz ? path_len : bufsiz;
  memcpy(buf, fake_app_path, copy_len);
  return (ssize_t)copy_len;
}

ssize_t readlink(const char *restrict path, char *restrict buf,
                 size_t bufsiz) {
  static readlink_fn libc_readlink;
  ssize_t result;
  int saved_errno;

  if (libc_readlink == NULL) {
    void *symbol = dlsym(RTLD_NEXT, "readlink");
    memcpy(&libc_readlink, &symbol, sizeof(libc_readlink));
  }
  if (libc_readlink == NULL) {
    errno = ENOSYS;
    result = -1;
  } else {
    result = libc_readlink(path, buf, bufsiz);
  }
  if (result >= 0 || !is_current_process_exe(path)) {
    return result;
  }

  saved_errno = errno;
  result = copy_fake_app_path(buf, bufsiz);
  if (result == -2) {
    errno = saved_errno;
    return -1;
  }
  return result;
}
