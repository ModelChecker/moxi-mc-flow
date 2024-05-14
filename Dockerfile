FROM python:3.11

RUN apt-get update && apt-get -y install \
        gcc-multilib xutils-dev flex bison vim
RUN pip install jsonschema

ENV HOME=/home
WORKDIR $HOME
COPY Dockerfile .

# README/LICENSE
COPY README.txt .
COPY LICENSE.txt LICENSE/
COPY LICENSE-avr.txt LICENSE/
COPY LICENSE-boolector.txt LICENSE/
COPY LICENSE-btor2tools.txt LICENSE/
COPY LICENSE-nuXmv.txt LICENSE/
COPY LICENSE-pono.txt LICENSE/

# src/test files
COPY src/ moxi-mc-flow/src/
COPY test/ moxi-mc-flow/test/
COPY benchmarks/ moxi-mc-flow/benchmarks/
COPY sortcheck.py moxi-mc-flow/
COPY modelcheck.py moxi-mc-flow/
COPY translate.py moxi-mc-flow/

COPY json-schema json-schema/

# scripts
COPY run_benchmarks_full.sh scripts/
COPY run_benchmarks_short.sh scripts/
COPY run_translate.sh scripts/
COPY run_modelcheck.sh scripts/
COPY run_sortcheck.sh scripts/
COPY run_jsonschema.sh scripts/

RUN chmod +x scripts/run_benchmarks_full.sh
RUN chmod +x scripts/run_benchmarks_short.sh
RUN chmod +x scripts/run_translate.sh
RUN chmod +x scripts/run_modelcheck.sh
RUN chmod +x scripts/run_sortcheck.sh
RUN chmod +x scripts/run_jsonschema.sh

# dependencies
COPY nuXmv-2.0.0-Linux/bin/nuXmv .
COPY avr/ avr/
COPY boolector/build/bin/btormc .
COPY pono/build/pono .
COPY pono/build/libpono.so /usr/lib
COPY btor2tools/build/bin/catbtor .
COPY btor2tools/build/lib/libbtor2parser.so /usr/lib

WORKDIR $HOME
CMD ["/bin/bash"]