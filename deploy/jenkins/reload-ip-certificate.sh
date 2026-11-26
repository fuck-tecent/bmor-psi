#!/usr/bin/env bash
set -euo pipefail

source_dir=/opt/goldbach-ci/ip-certificate/production/config/live/goldbach-webhook-ip
destination=/etc/caddy/ip-tls
if cmp -s "$source_dir/fullchain.pem" "$destination/current/fullchain.pem" &&
    cmp -s "$source_dir/privkey.pem" "$destination/current/privkey.pem"; then
    exit 0
fi
openssl verify -verify_ip 114.55.113.128 -untrusted "$source_dir/chain.pem" "$source_dir/cert.pem"
install -d -m 0750 -o root -g caddy "$destination"
next=$(mktemp -d "$destination/cert.XXXXXX")
chown root:caddy "$next"
chmod 0750 "$next"
install -m 0640 -o root -g caddy "$source_dir/fullchain.pem" "$source_dir/privkey.pem" "$next/"

previous=$(readlink "$destination/current" || true)
ln -s "$(basename "$next")" "$next.link"
mv -Tf "$next.link" "$destination/current"
if ! systemctl reload caddy; then
    if [[ -n "$previous" ]]; then
        ln -s "$previous" "$next.link"
        mv -Tf "$next.link" "$destination/current"
    else
        rm -f "$destination/current"
    fi
    exit 1
fi
