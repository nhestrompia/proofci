#include <arpa/inet.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>

int main(int argc, char **argv) {
    if (argc != 3) return 2;
    int fd;
    int result;
    if (strcmp(argv[1], "unix") == 0) {
        struct sockaddr_un address = {.sun_family = AF_UNIX};
        if (strlen(argv[2]) >= sizeof(address.sun_path)) return 2;
        strcpy(address.sun_path, argv[2]);
        fd = socket(AF_UNIX, SOCK_STREAM, 0);
        if (fd < 0) return 2;
        result = connect(fd, (struct sockaddr *)&address, sizeof(address));
    } else if (strcmp(argv[1], "tcp") == 0) {
        struct sockaddr_in address = {.sin_family = AF_INET, .sin_port = htons(443)};
        if (inet_pton(AF_INET, argv[2], &address.sin_addr) != 1) return 2;
        fd = socket(AF_INET, SOCK_STREAM, 0);
        if (fd < 0) return 2;
        result = connect(fd, (struct sockaddr *)&address, sizeof(address));
    } else {
        return 2;
    }
    close(fd);
    return result == 0 ? 0 : 1;
}
