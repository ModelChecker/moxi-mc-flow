FROM python:3.11

RUN apt-get update && apt-get -y install \
        gcc-multilib xutils-dev flex bison vim
RUN pip install jsonschema

ENV HOME=/home
WORKDIR $HOME

COPY Dockerfile .
COPY README.txt .

# src/test files
COPY src/ moxi-mc-flow/src/
COPY test/ moxi-mc-flow/test/
COPY benchmarks/ moxi-mc-flow/benchmarks/
COPY sortcheck.py moxi-mc-flow/
COPY modelcheck.py moxi-mc-flow/
COPY translate.py moxi-mc-flow/

COPY json-schema json-schema/

# scripts
COPY scripts/ scripts/

RUN chmod +x scripts/run_benchmarks_full.sh
RUN chmod +x scripts/run_benchmarks_short.sh
RUN chmod +x scripts/run_translate.sh
RUN chmod +x scripts/run_modelcheck.sh
RUN chmod +x scripts/run_sortcheck.sh
RUN chmod +x scripts/run_jsonschema.sh

# dependencies
COPY deps/nuXmv-2.0.0-Linux/bin/nuXmv deps/
COPY deps/avr/ deps/avr/
COPY deps/boolector/build/bin/btormc deps/
COPY deps/pono/build/pono deps/
COPY deps/pono/build/libpono.so /usr/lib
COPY deps/btor2tools/build/bin/catbtor deps/
COPY deps/btor2tools/build/lib/libbtor2parser.so /usr/lib

# LICENSES
COPY LICENSE.txt .
COPY deps/LICENSE* deps/

WORKDIR $HOME
CMD ["/bin/bash"]