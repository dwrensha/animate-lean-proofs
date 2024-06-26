# Animate Lean Proofs

Code from [this video](https://youtu.be/KuxFWwwlEtc).

[<img src="http://img.youtube.com/vi/KuxFWwwlEtc/maxresdefault.jpg" height="240px">](http://youtu.be/KuxFWwwlEtc)

## running

```shell
$ lake exe cache get
$ lake exe Animate Input/NNG.lean NNG.mul_pow > /tmp/mul_pow.json
$ blender --python animate_proof.py -- /tmp/mul_pow.json
```

(I've been using blender v4.0.2.)


