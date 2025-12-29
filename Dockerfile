FROM python:3.12-slim

ENV DEBIAN_FRONTEND=noninteractive \
    PIP_NO_CACHE_DIR=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    OQS_INSTALL_PATH=/usr/local \
    LD_LIBRARY_PATH=/usr/local/lib:${LD_LIBRARY_PATH}

# ------------------------------------------------------------
# System deps
# ------------------------------------------------------------
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    cmake \
    ninja-build \
    build-essential \
    pkg-config \
 && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# ------------------------------------------------------------
# PQ provenance inputs
# ------------------------------------------------------------
COPY lock.manifest.json lock.manifest.pqsig pq_pubkey.b64 requirements.txt ./

# ------------------------------------------------------------
# Build liboqs (C) with SHA256 pin
# ------------------------------------------------------------
ARG LIBOQS_VERSION=0.14.0
ARG LIBOQS_TARBALL_SHA256=5b0df6138763b3fc4e385d58dbb2ee7c7c508a64a413d76a917529e3a9a207ea

RUN set -euo pipefail \
 && curl -fsSL -o /tmp/liboqs.tar.gz \
      "https://github.com/open-quantum-safe/liboqs/archive/refs/tags/${LIBOQS_VERSION}.tar.gz" \
 && echo "${LIBOQS_TARBALL_SHA256}  /tmp/liboqs.tar.gz" | sha256sum -c - \
 && mkdir -p /tmp/liboqs-src \
 && tar -xzf /tmp/liboqs.tar.gz -C /tmp/liboqs-src --strip-components=1 \
 && cmake -S /tmp/liboqs-src -B /tmp/liboqs-src/build \
      -DCMAKE_INSTALL_PREFIX=/usr/local \
      -DBUILD_SHARED_LIBS=ON \
      -DOQS_USE_OPENSSL=OFF \
      -DCMAKE_POSITION_INDEPENDENT_CODE=ON \
      -G Ninja \
 && cmake --build /tmp/liboqs-src/build --parallel \
 && cmake --install /tmp/liboqs-src/build \
 && ldconfig \
 && rm -rf /tmp/liboqs.tar.gz /tmp/liboqs-src

# ------------------------------------------------------------
# Bootstrap minimal Python for PQ verification
# ------------------------------------------------------------
RUN python -m pip install --upgrade pip

RUN cat > /tmp/pq_bootstrap.txt <<'REQ'
cffi==2.0.0 \
    --hash=sha256:00bdf7acc5f795150faa6957054fbbca2439db2f775ce831222b66f192f03beb \
    --hash=sha256:07b271772c100085dd28b74fa0cd81c8fb1a3ba18b21e03d7c27f3436a10606b
pycparser==2.23 \
    --hash=sha256:78816d4f24add8f10a06d6f05b4d424ad9e96cfebf68a4ddc99c65c0720d00c2 \
    --hash=sha256:e5c6e8d3fbad53479cab09ac03729e0a9faf2bee3db8208a550daf5af81a5934
liboqs-python==0.14.1 \
    --hash=sha256:e3c81e632d02122dda3734edc4ba83bd457eefa3fdb266d33ea908a77a17642f
REQ

RUN set -euo pipefail \
 && python -m pip install --no-cache-dir --require-hashes -r /tmp/pq_bootstrap.txt \
 && rm -f /tmp/pq_bootstrap.txt

# ------------------------------------------------------------
# PQ authenticity verification (Dilithium)
# ------------------------------------------------------------
RUN python <<'PY'
import base64, hashlib, json, sys, pathlib
import oqs

manifest = pathlib.Path("lock.manifest.json")
sig = pathlib.Path("lock.manifest.pqsig")
pub = pathlib.Path("pq_pubkey.b64")
req = pathlib.Path("requirements.txt")

for p in (manifest, sig, pub, req):
    if not p.exists():
        print(f"ERROR: missing {p}", file=sys.stderr)
        sys.exit(2)

msg = manifest.read_bytes()
signature = base64.b64decode(sig.read_text().strip())
pubkey = base64.b64decode(pub.read_text().strip())

with oqs.Signature("Dilithium2") as v:
    if not v.verify(msg, signature, pubkey):
        print("ERROR: PQ signature verification failed", file=sys.stderr)
        sys.exit(3)

expected = json.loads(msg)["requirements_txt_sha256"]
actual = hashlib.sha256(req.read_bytes()).hexdigest()

if actual != expected:
    print("ERROR: requirements.txt SHA256 mismatch", file=sys.stderr)
    print("expected:", expected, file=sys.stderr)
    print("actual:  ", actual, file=sys.stderr)
    sys.exit(4)

print("OK: PQ verification successful")
PY

# ------------------------------------------------------------
# Install full dependency graph (hash locked)
# ------------------------------------------------------------
RUN python -m pip install --no-cache-dir --require-hashes -r requirements.txt

# ------------------------------------------------------------
# App
# ------------------------------------------------------------
COPY . .

RUN useradd -ms /bin/bash appuser \
 && mkdir -p /app/static \
 && chown -R appuser:appuser /app

USER appuser

EXPOSE 3000

CMD ["gunicorn","main:app","-b","0.0.0.0:3000","-w","4","-k","gthread","--threads","4","--timeout","180","--graceful-timeout","30","--log-level","info","--preload","--max-requests","1000","--max-requests-jitter","200"]
