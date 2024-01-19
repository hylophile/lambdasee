#!/usr/bin/env sh

cargo build --release
cp target/release/lambdasee .
patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 lambdasee

rclone copy -LP lambdasee mve:web/web/lambdasee/
rm lambdasee
rclone copy -LP src/html/ mve:web/web/lambdasee/src/html

# pkill lambdasee || cd web/web/lambdasee && chmod +x lambdasee && nohup ./lambdasee > /var/log/lambdasee.log 2>&1 &
