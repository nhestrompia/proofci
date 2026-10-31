#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

static void limit(int resource, rlim_t value) {
    struct rlimit bounds = {value, value};
    if (setrlimit(resource, &bounds) != 0) _exit(2);
}

static void exercise(const char *name) {
    if (setgid(1000) || setuid(1000)) _exit(2);
    if (!strcmp(name, "cpu")) {
        limit(RLIMIT_CPU, 1);
        for (;;) {}
    }
    if (!strcmp(name, "memory")) {
        limit(RLIMIT_AS, 16 * 1024 * 1024);
        void *p = malloc(64 * 1024 * 1024);
        _exit(p == NULL ? 42 : 3);
    }
    if (!strcmp(name, "disk")) {
        signal(SIGXFSZ, SIG_IGN);
        limit(RLIMIT_FSIZE, 4096);
        int fd = open("/tmp/limit-data", O_CREAT | O_WRONLY | O_TRUNC, 0600);
        if (fd < 0) _exit(2);
        char buf[4096] = {0};
        if (write(fd, buf, sizeof(buf)) != sizeof(buf)) _exit(2);
        _exit(write(fd, buf, sizeof(buf)) < 0 && errno == EFBIG ? 42 : 3);
    }
    if (!strcmp(name, "processes")) {
        limit(RLIMIT_NPROC, 8);
        for (int i = 0; i < 20; i++) {
            pid_t child = fork();
            if (child == 0) { sleep(15); _exit(0); }
            if (child < 0) _exit(errno == EAGAIN ? 42 : 2);
        }
        _exit(3);
    }
    _exit(2);
}

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    pid_t child = fork();
    if (child < 0) return 2;
    if (child == 0) { setpgid(0, 0); exercise(argv[1]); }
    setpgid(child, child);
    int status;
    if (waitpid(child, &status, 0) < 0) return 2;
    kill(-child, SIGKILL);
    if (!strcmp(argv[1], "cpu")) return WIFSIGNALED(status) && WTERMSIG(status) == SIGKILL ? 0 : 1;
    return WIFEXITED(status) && WEXITSTATUS(status) == 42 ? 0 : 1;
}
