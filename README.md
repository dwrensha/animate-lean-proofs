# Animate Lean Proofs

This is a tool that accepts as input any Lean 4 theorem,
and produces as output a Blender animation showing
the steps of the proof smoothly evolving in sequence.

[This video](https://youtu.be/KuxFWwwlEtc) provides some more background
and shows some examples.

[<img src="http://img.youtube.com/vi/KuxFWwwlEtc/maxresdefault.jpg" height="240px">](http://youtu.be/KuxFWwwlEtc)

## more examples

|  |  |
| ----- | ---- |
| IMO 2024 Problem 2 | [<img src="http://img.youtube.com/vi/5IARsdn78xE/maxresdefault.jpg" height="120px">](https://youtu.be/5IARsdn78xE)|

| IMO 1987 Problem 4 | [<img src="http://img.youtube.com/vi/gi8ZTjRO-xI/maxresdefault.jpg" height="120px">](https://youtu.be/gi8ZTjRO-xI)|


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




