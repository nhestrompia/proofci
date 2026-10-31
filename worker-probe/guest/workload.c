#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    if (setgid(1000) || setuid(1000)) return 2;
    if (strcmp(argv[1], "cpu") == 0) {
        for (;;) {}
    }
    if (strcmp(argv[1], "memory") == 0) {
        for (;;) {
            char *p = malloc(1024 * 1024);
            if (!p) return 3;
            for (size_t i = 0; i < 1024 * 1024; i += 4096) p[i] = 1;
        }
    }
    if (strcmp(argv[1], "disk") == 0) {
        int fd = open("/data", O_CREAT | O_WRONLY | O_TRUNC, 0600);
        if (fd < 0) return 2;
        char data[4096] = {0};
        for (;;) {
            ssize_t written = write(fd, data, sizeof(data));
            if (written < 0) return errno == ENOSPC ? 42 : 2;
            if (written == 0) return 2;
        }
    }
    if (strcmp(argv[1], "pids") == 0) {
        for (int i = 0; i < 32; i++) {
            pid_t pid = fork();
            if (pid == 0) { sleep(30); _exit(0); }
            if (pid < 0) return errno == EAGAIN ? 42 : 2;
        }
        return 3;
    }
    return 2;
}
