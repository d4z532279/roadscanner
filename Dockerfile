FROM python:3.12-slim

ENV DEBIAN_FRONTEND=noninteractive \
    PIP_NO_CACHE_DIR=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    OQS_INSTALL_PATH=/usr/local \
    LD_LIBRARY_PATH=/usr/local/lib:${LD_LIBRARY_PATH}

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    cmake \
    ninja-build \
    build-essential \
    pkg-config \
 && rm -rf /var/lib/apt/lists/*

WORKDIR /app

ARG LIBOQS_VERSION=0.14.0
ARG LIBOQS_TARBALL_SHA256=5b0df6138763b3fc4e385d58dbb2ee7c7c508a64a413d76a917529e3a9a207ea

RUN set -euo pipefail; \
    curl -fsSL -o /tmp/liboqs.tar.gz \
      "https://github.com/open-quantum-safe/liboqs/archive/refs/tags/${LIBOQS_VERSION}.tar.gz"; \
    echo "${LIBOQS_TARBALL_SHA256}  /tmp/liboqs.tar.gz" | sha256sum -c -; \
    mkdir -p /tmp/liboqs-src; \
    tar -xzf /tmp/liboqs.tar.gz -C /tmp/liboqs-src --strip-components=1; \
    cmake -S /tmp/liboqs-src -B /tmp/liboqs-src/build \
      -DCMAKE_INSTALL_PREFIX=/usr/local \
      -DBUILD_SHARED_LIBS=ON \
      -DOQS_USE_OPENSSL=OFF \
      -DCMAKE_POSITION_INDEPENDENT_CODE=ON \
      -G Ninja; \
    cmake --build /tmp/liboqs-src/build --parallel; \
    cmake --install /tmp/liboqs-src/build; \
    ldconfig; \
    rm -rf /tmp/liboqs.tar.gz /tmp/liboqs-src

ARG LIBOQS_PY_VERSION=0.12.0
ARG LIBOQS_PY_TARBALL_SHA256=9a92e781800a3a3ea83a2ccfb4f81211cacd38f34b98b40df59f2023494102d6

RUN set -euo pipefail; \
    curl -fsSL -o /tmp/liboqs-python.tar.gz \
      "https://github.com/open-quantum-safe/liboqs-python/archive/refs/tags/${LIBOQS_PY_VERSION}.tar.gz"; \
    echo "${LIBOQS_PY_TARBALL_SHA256}  /tmp/liboqs-python.tar.gz" | sha256sum -c -; \
    mkdir -p /tmp/liboqs-python-src; \
    tar -xzf /tmp/liboqs-python.tar.gz -C /tmp/liboqs-python-src --strip-components=1; \
    cd /tmp/liboqs-python-src; \
    cmake -S . -B build \
      -DCMAKE_PREFIX_PATH=/usr/local; \
    cmake --build build --parallel; \
    pip install --no-cache-dir dist/*.whl; \
    rm -rf /tmp/liboqs-python.tar.gz /tmp/liboqs-python-src

COPY requirements.txt .
RUN pip install --no-cache-dir --require-hashes -r requirements.txt

COPY . .

RUN useradd -ms /bin/bash appuser \
 && mkdir -p /app/static \
 && chmod 755 /app/static \
 && chown -R appuser:appuser /app

USER appuser

EXPOSE 3000

CMD ["gunicorn","main:app","-b","0.0.0.0:3000","-w","4","-k","gthread","--threads","4","--timeout","180","--graceful-timeout","30","--log-level","info","--preload","--max-requests","1000","--max-requests-jitter","200"]
