# Animate Lean Proofs

Code from [this video](https://youtu.be/KuxFWwwlEtc).

[<img src="http://img.youtube.com/vi/KuxFWwwlEtc/maxresdefault.jpg" height="240px">](http://youtu.be/KuxFWwwlEtc)

## setup

1. Install [Blender](https://www.blender.org/).
   I've been using v4.0.2, but any recentish version should work.

2. Install Pygments:
```shell
$ pip install pygments
```

## running

```shell
$ lake exe cache get
$ lake exe Animate Input/NNG.lean NNG.mul_pow > /tmp/mul_pow.json
$ blender --python animate_proof.py -- /tmp/mul_pow.json
```




