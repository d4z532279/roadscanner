import os
from pathlib import Path

os.environ.setdefault("INVITE_CODE_SECRET_KEY", "test_invite_secret_12345")
os.environ.setdefault("ENCRYPTION_PASSPHRASE", "TestPassphrase123!@#")
os.environ.setdefault("STRICT_PQ2_ONLY", "0")
os.environ.setdefault("admin_username", "admin")
os.environ.setdefault("admin_pass", "StrongPass1!")

import main


def test_x_synthetic_payload():
    os.environ["RGN_X_TEST_API"] = "synthetic"
    os.environ["RGN_X_TEST_SEED"] = "7"
    payload = main._x2_fetch_payload_from_env(
        bearer="test_bearer",
        x_user_id="test_user",
        max_results=12,
    )
    assert isinstance(payload, dict)
    rows = main.x2_parse_tweets(payload, src="test")
    assert rows, "Expected synthetic tweet rows"
    assert all(row.get("tid") for row in rows)
    assert all(row.get("text") for row in rows)


def test_x_synthetic_roundtrip_db():
    os.environ["RGN_X_TEST_API"] = "synthetic"
    payload = main._x2_fetch_payload_from_env(
        bearer="test_bearer",
        x_user_id="test_user",
        max_results=6,
    )
    rows = main.x2_parse_tweets(payload, src="test")
    Path("/var/data").mkdir(parents=True, exist_ok=True)
    main.create_tables()
    inserted = main.x2_upsert_tweets(owner_user_id=1, rows=rows)
    assert inserted >= 1
    listed = main.x2_list_tweets(owner_user_id=1, limit=10)
    assert listed, "Expected tweets persisted to DB"


if __name__ == "__main__":
    test_x_synthetic_payload()
    test_x_synthetic_roundtrip_db()
    print("Synthetic X feed tests passed.")
