# syntax=docker/dockerfile:1
FROM python:3.12-slim

ENV DEBIAN_FRONTEND=noninteractive \
    PIP_NO_CACHE_DIR=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    OQS_INSTALL_PATH=/usr/local \
    LD_LIBRARY_PATH=/usr/local/lib:${LD_LIBRARY_PATH}

# ---- system deps (build + verify) ----
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    cmake \
    ninja-build \
    build-essential \
    pkg-config \
    python3-dev \
 && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# ---- build + verify liboqs (pinned + sha256) ----
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

# ---- build + verify liboqs-python (PINNED + sha256) ----
# This is the Python package that provides `import oqs`
ARG LIBOQS_PY_VERSION=0.12.0
ARG LIBOQS_PY_TARBALL_SHA256=9a92e781800a3a3ea83a2ccfb4f81211cacd38f34b98b40df59f2023494102d6

RUN set -euo pipefail; \
    curl -fsSL -o /tmp/liboqs-python.tar.gz \
      "https://github.com/open-quantum-safe/liboqs-python/archive/refs/tags/${LIBOQS_PY_VERSION}.tar.gz"; \
    echo "${LIBOQS_PY_TARBALL_SHA256}  /tmp/liboqs-python.tar.gz" | sha256sum -c -; \
    mkdir -p /tmp/liboqs-python-src; \
    tar -xzf /tmp/liboqs-python.tar.gz -C /tmp/liboqs-python-src --strip-components=1; \
    cd /tmp/liboqs-python-src; \
    cmake -S . -B build -DCMAKE_PREFIX_PATH=/usr/local -G Ninja; \
    cmake --build build --parallel; \
    # installs the built wheel (pins to the tarball tag above)
    pip install --no-cache-dir dist/*.whl; \
    rm -rf /tmp/liboqs-python.tar.gz /tmp/liboqs-python-src

# ---- copy PQ manifest + signature + pubkey from REPO ROOT ----
# (you said they are NOT in ./pq/, they're in the base repo dir)
COPY lock.manifest.json lock.manifest.pqsig pq_pubkey.b64 ./

# ---- copy requirements + verify against PQ manifest BEFORE pip install ----
COPY requirements.txt ./

# Verifies:
#  1) requirements.txt sha256 matches lock.manifest.json requirements_txt_sha256
#  2) Dilithium2 signature in lock.manifest.pqsig verifies over the exact bytes of lock.manifest.json
#     using pq_pubkey.b64 (base64 pubkey)
#
# Signature file can be either raw bytes or base64 text; this handles both.
RUN set -euo pipefail; \
    python - <<'PY' \
import base64, binascii, hashlib, json, os, sys \
\
MANIFEST = "lock.manifest.json" \
SIGFILE  = "lock.manifest.pqsig" \
PUBFILE  = "pq_pubkey.b64" \
\
# 1) requirements.txt sha256 check \
with open(MANIFEST, "rb") as f: \
    manifest_bytes = f.read() \
manifest = json.loads(manifest_bytes.decode("utf-8")) \
expected_req_sha = manifest.get("requirements_txt_sha256") \
if not expected_req_sha: \
    raise SystemExit("lock.manifest.json missing requirements_txt_sha256") \
\
h = hashlib.sha256() \
with open("requirements.txt", "rb") as f: \
    for chunk in iter(lambda: f.read(1024 * 1024), b""): \
        h.update(chunk) \
actual_req_sha = h.hexdigest() \
if actual_req_sha != expected_req_sha: \
    raise SystemExit(f"requirements.txt sha256 mismatch: expected {expected_req_sha} got {actual_req_sha}") \
\
# 2) PQ signature verify over *exact manifest bytes* \
# pubkey is base64 text \
pub_b64 = open(PUBFILE, "rb").read().strip() \
pubkey = base64.b64decode(pub_b64) \
\
sig_raw = open(SIGFILE, "rb").read().strip() \
# Try: if it's base64 text, decode; else treat as raw signature \
try: \
    # accept common "base64 text" signatures \
    sig = base64.b64decode(sig_raw, validate=True) \
    # If validate=True succeeded but produced empty, fallback to raw \
    if not sig: \
        sig = sig_raw \
except (binascii.Error, ValueError): \
    sig = sig_raw \
\
pq_alg = manifest.get("pq_alg", "Dilithium2") \
try: \
    import oqs \
except Exception as e: \
    raise SystemExit(f"failed to import oqs (liboqs-python): {e}") \
\
with oqs.Signature(pq_alg) as s: \
    ok = s.verify(manifest_bytes, sig, pubkey) \
if not ok: \
    raise SystemExit(f"PQ signature verify FAILED (alg={pq_alg})") \
\
print(f"PQ verify OK (alg={pq_alg}); requirements.txt sha256 OK") \
PY

# ---- install dependencies (hash-locked) ----
RUN pip install --no-cache-dir --require-hashes -r requirements.txt

# ---- app sources ----
COPY . .

# ---- non-root runtime ----
RUN useradd -ms /bin/bash appuser \
 && mkdir -p /app/static \
 && chmod 755 /app/static \
 && chown -R appuser:appuser /app

USER appuser

EXPOSE 3000

CMD ["gunicorn","main:app","-b","0.0.0.0:3000","-w","4","-k","gthread","--threads","4","--timeout","180","--graceful-timeout","30","--log-level","info","--preload","--max-requests","1000","--max-requests-jitter","200"]
