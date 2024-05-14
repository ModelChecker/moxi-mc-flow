FROM python:3.11

RUN apt-get update && apt-get -y install \
        gcc-multilib xutils-dev flex bison vim
RUN pip install jsonschema

ENV HOME=/home
WORKDIR $HOME

COPY Dockerfile .
COPY README.txt .
COPY LICENSE.txt .

# src/test files
COPY src/ src/
COPY test/ test/
COPY benchmarks/ benchmarks/
COPY sortcheck.py .
COPY modelcheck.py .
COPY translate.py .

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
COPY deps/LICENSE* deps/
COPY deps/avr deps/
COPY deps/catbtor deps/
COPY deps/nuXmv deps/
COPY deps/btormc deps/
COPY deps/pono deps/

WORKDIR $HOME
CMD ["/bin/bash"]