# syntax=docker/dockerfile:1

FROM python:3.12-slim

ENV DEBIAN_FRONTEND=noninteractive \
    PIP_NO_CACHE_DIR=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    OQS_INSTALL_PATH=/usr/local \
    LD_LIBRARY_PATH=/usr/local/lib:${LD_LIBRARY_PATH}

# ------------------------------
# System deps
# ------------------------------
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    cmake \
    ninja-build \
    build-essential \
    pkg-config \
 && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# ------------------------------
# Copy PQ verification assets (you said they're in repo root)
#   - lock.manifest.json
#   - lock.manifest.pqsig
#   - pq_pubkey.b64
# ------------------------------
COPY lock.manifest.json lock.manifest.json
COPY lock.manifest.pqsig lock.manifest.pqsig
COPY pq_pubkey.b64 pq_pubkey.b64

# ------------------------------
# Build + install liboqs (SHA256 verified)
# ------------------------------
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

# ------------------------------
# Build + install liboqs-python (SHA256 verified)
# ------------------------------
ARG LIBOQS_PY_VERSION=0.12.0
ARG LIBOQS_PY_TARBALL_SHA256=9a92e781800a3a3ea83a2ccfb4f81211cacd38f34b98b40df59f2023494102d6

RUN set -euo pipefail; \
    curl -fsSL -o /tmp/liboqs-python.tar.gz \
      "https://github.com/open-quantum-safe/liboqs-python/archive/refs/tags/${LIBOQS_PY_VERSION}.tar.gz"; \
    echo "${LIBOQS_PY_TARBALL_SHA256}  /tmp/liboqs-python.tar.gz" | sha256sum -c -; \
    mkdir -p /tmp/liboqs-python-src; \
    tar -xzf /tmp/liboqs-python.tar.gz -C /tmp/liboqs-python-src --strip-components=1; \
    cd /tmp/liboqs-python-src; \
    cmake -S . -B build -DCMAKE_PREFIX_PATH=/usr/local; \
    cmake --build build --parallel; \
    python -m pip install --upgrade pip; \
    python -m pip install --no-cache-dir dist/*.whl; \
    rm -rf /tmp/liboqs-python.tar.gz /tmp/liboqs-python-src

# ------------------------------
# Pin pyoqs (Python API layer) so PQ verification is deterministic
# ------------------------------
ARG PYOQS_VERSION=0.14.0
RUN set -euo pipefail; \
    python -m pip install --no-cache-dir "pyoqs==${PYOQS_VERSION}"; \
    python - <<'PY' \
import oqs; \
print("pyoqs ok, liboqs version:", oqs.oqs_version()) \
PY

# ------------------------------
# PQ authenticity gate:
#   - verify Dilithium2 signature over lock.manifest.json
#   - verify manifest's SHA256 matches requirements.txt content
# Fails the build if anything is wrong.
# ------------------------------
ARG PQSIG_ALG=Dilithium2

# Copy requirements before verification so we can hash it
COPY requirements.txt requirements.txt

RUN set -euo pipefail; \
    python - <<'PY' \
import base64, hashlib, json, os, sys \
import oqs \
ALG = os.environ.get("PQSIG_ALG","Dilithium2") \
 \
def die(msg, code=2): \
    print("ERROR:", msg, file=sys.stderr) \
    sys.exit(code) \
 \
for p in ("lock.manifest.json","lock.manifest.pqsig","pq_pubkey.b64","requirements.txt"): \
    if not os.path.exists(p): \
        die(f"missing required file: {p}", 10) \
 \
# Load pubkey \
with open("pq_pubkey.b64","rb") as f: \
    pub = base64.b64decode(f.read().strip()) \
 \
# Load manifest bytes + signature \
manifest_bytes = open("lock.manifest.json","rb").read() \
sig = open("lock.manifest.pqsig","rb").read() \
 \
# Verify signature over manifest bytes \
with oqs.Signature(ALG) as v: \
    ok = v.verify(manifest_bytes, sig, pub) \
if not ok: \
    die("PQ signature verification FAILED for lock.manifest.json", 20) \
 \
# Parse manifest + verify it binds requirements.txt sha256 \
try: \
    man = json.loads(manifest_bytes.decode("utf-8")) \
except Exception as e: \
    die(f"manifest JSON parse failed: {e}", 21) \
 \
req_sha_expected = (man.get("requirements_txt_sha256") or "").strip().lower() \
if len(req_sha_expected) != 64 or any(c not in "0123456789abcdef" for c in req_sha_expected): \
    die("manifest missing/invalid requirements_txt_sha256", 22) \
 \
req_bytes = open("requirements.txt","rb").read() \
req_sha_actual = hashlib.sha256(req_bytes).hexdigest() \
if req_sha_actual != req_sha_expected: \
    die(f"requirements.txt sha256 mismatch: expected {req_sha_expected} got {req_sha_actual}", 23) \
 \
print("OK: PQ signature valid + manifest binds requirements.txt sha256") \
PY

# ------------------------------
# Install Python deps (hash-locked)
# ------------------------------
RUN pip install --no-cache-dir --require-hashes -r requirements.txt

# ------------------------------
# App copy
# ------------------------------
COPY . .

# ------------------------------
# Create unprivileged user
# ------------------------------
RUN useradd -ms /bin/bash appuser \
 && mkdir -p /app/static \
 && chmod 755 /app/static \
 && chown -R appuser:appuser /app

USER appuser

EXPOSE 3000

CMD ["gunicorn","main:app","-b","0.0.0.0:3000","-w","4","-k","gthread","--threads","4","--timeout","180","--graceful-timeout","30","--log-level","info","--preload","--max-requests","1000","--max-requests-jitter","200"]
