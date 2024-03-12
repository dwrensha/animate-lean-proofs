animation: pngs
	ffmpeg -framerate 24 -i  /tmp/out/%04d.png '-c:v' libx264 -pix_fmt yuv420p /tmp/output.mp4

pngs:
	RENDER=true \
	OUTDIR=/tmp/out/ \
	  blender --background --python animate.py
