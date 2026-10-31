FROM alpine:3.22 AS build
RUN apk add --no-cache build-base
COPY guest/connect.c guest/limits.c guest/workload.c /
RUN cc -static -O2 -Wall -Wextra -Werror -o /connect /connect.c && cc -static -O2 -Wall -Wextra -Werror -o /limits /limits.c && cc -static -O0 -Wall -Wextra -Werror -o /workload /workload.c

FROM alpine:3.22
RUN apk add --no-cache qemu-system-aarch64 linux-virt busybox-static cpio python3
COPY --from=build /connect /limits /workload /
COPY guest/init /guest-init
COPY run.py /run.py
ENTRYPOINT ["python3", "/run.py"]
