FROM python@sha256:6a9220edda062e9223ea0784740a535987299420b96fbfd520b89bbd3e772485
COPY --from=lean / /lean/
COPY --from=bubblewrap /usr/bin/bwrap /usr/bin/bwrap
COPY experiments/source-binding/evidence.py experiments/source-binding/binding.py experiments/source-binding/admission.py experiments/source-binding/toolchain.py experiments/source-binding/core-dependencies.json /app/experiments/source-binding/
COPY portable/proofci.py portable/scope.py /app/portable/
RUN test "$(sha256sum /usr/bin/bwrap | cut -d' ' -f1)" = b3b829e18a7d43ee589dc37e351cb9480ff7301b493d8227b8c754294638b976 \
 && test "$(python3 /app/experiments/source-binding/toolchain.py /lean)" = ad4f844f85ce90b22e30efee3a1028ea99d15724fe72de7dc4e16ceda971da00 \
 && mkdir /runinput /result
USER 65534:65534
ENV HOME=/tmp PROOFCI_CONTAINER=1
ENTRYPOINT ["python3", "/app/portable/proofci.py"]
