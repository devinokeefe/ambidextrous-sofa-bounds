"""Makes four corrupted versions of the 9/5 certificate, each of which a checker must reject:
  trunc        the last 1000 tokens deleted;
  lowT         the threshold lowered to 179/100;
  tamper       a subtree 'k L L' after the middle of the file merged into one leaf;
  tampersplit  the coordinate of the first bisection changed.
Run from the data folder; writes controls/NAME.json and controls/cert_NAME.txt.
"""

import json
import os

with open("specs/c_3653_18_10.json") as fh:
    spec = json.load(fh)
with open(spec["cert"]) as fh:
    tokens = fh.read().split()
os.makedirs("controls", exist_ok=True)


def write(name, new_tokens=None, T=None):
    s = dict(spec)
    if new_tokens is not None:
        s["cert"] = f"controls/cert_{name}.txt"
        with open(s["cert"], "w") as fh:
            fh.write(" ".join(new_tokens))
    if T:
        s["T"] = T
    with open(f"controls/{name}.json", "w") as fh:
        json.dump(s, fh)


write("trunc", tokens[:-1000])
write("lowT", T="179/100")
i = len(tokens) // 2
while not (tokens[i] != "L" and tokens[i + 1] == "L" and tokens[i + 2] == "L"):
    i += 1
write("tamper", [*tokens[:i], "L", *tokens[i + 3 :]])
print("tamper: position", i, "split coordinate", tokens[i])
write("tampersplit", [str((int(tokens[0]) + 1) % 8), *tokens[1:]])
