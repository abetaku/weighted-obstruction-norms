#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
/* Runtime path compatibility only: both paths identify this very process.
   All other readlink operations are forwarded without modification. */
ssize_t readlink(const char *path, char *buf, size_t size) {
  ssize_t (*real_readlink)(const char*,char*,size_t) = dlsym(RTLD_NEXT, "readlink");
  char self[64];
  snprintf(self, sizeof(self), "/proc/%d/exe", (int)getpid());
  return real_readlink(strcmp(path, self) == 0 ? "/proc/self/exe" : path, buf, size);
}
