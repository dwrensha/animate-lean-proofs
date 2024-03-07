import os
import bpy

TILE_THICK = 0.2
yellowColor = (0.95, 0.829, 0.05, 1)
brownColor = (0.0451939, 0.00518128, 0.00802261, 1)

# got this from
# https://blender.stackexchange.com/questions/104651/selecting-gpu-with-python-script
def use_gpu_render():
    bpy.data.scenes[0].render.engine = "CYCLES"

    # Set the device_type
    bpy.context.preferences.addons[
        "cycles"
    ].preferences.compute_device_type = "CUDA" # or "OPENCL"

    # Set the device and feature set
    bpy.context.scene.cycles.device = "GPU"

    # get_devices() to let Blender detects GPU device
    bpy.context.preferences.addons["cycles"].preferences.get_devices()
    print(bpy.context.preferences.addons["cycles"].preferences.compute_device_type)
    for d in bpy.context.preferences.addons["cycles"].preferences.devices:
        d["use"] = 1 # Using all devices, include GPU and CPU
        print(d["name"], d["use"])

use_gpu_render()

bpy.context.scene.cycles.feature_set = 'EXPERIMENTAL' # for adaptive subdivision
bpy.context.scene.cycles.dicing_rate = 0.25

bpy.context.scene.render.filepath = "/tmp/out.png"

bpy.context.scene.render.resolution_x = 1920
bpy.context.scene.render.resolution_y = 1080

# delete the default cube
if "Cube" in bpy.data.objects:
    bpy.data.objects['Cube'].select_set(True)
    bpy.context.view_layer.objects.active = bpy.data.objects['Cube']
    bpy.ops.object.delete()

#FONTPATH = "/home/dwrensha/fonts/DejaVuSansCondensed.ttf"
MONOFONTPATH = "/home/dwrensha/fonts/DejaVuSansMono.ttf"
MONOFONT = bpy.data.fonts.load(MONOFONTPATH)

class AtomizedText:
    def __init__(self, string, location = (0,0,0)):
        bpy.ops.object.text_add()
        cobj = bpy.context.object
        cobj.data.body = "M"
        cobj.data.font = MONOFONT
        bpy.context.view_layer.update()
        self.char_width=cobj.dimensions.x
        self.char_height=cobj.dimensions.y
        bpy.ops.object.delete()

        bpy.ops.object.empty_add(location=location)
        self.top = bpy.context.object
        self.top.name = "AtomizedText"
        self.lines = []
        yidx = 0
        for line in string.splitlines():
            print(line)
            xidx = 0

            bpy.ops.object.empty_add(location = (0,yidx * self.char_height * -1.8, 0))
            currentline = bpy.context.object
            currentline.parent = self.top

            for c in line:
                bpy.ops.object.text_add(location = (xidx * self.char_width, 0, 0))
                cobj = bpy.context.object
                cobj.data.body = c
                cobj.parent = currentline
                xidx += 1
                cobj.data.font = MONOFONT

            yidx += 1
            self.lines.append(currentline)

        pass

#bpy.ops.object.text_add(
#    enter_editmode=False, align='WORLD', location=(0, 0, 0), scale=(1, 1, 1))
#bpy.context.object.name = "Math1"

math1 = """f : ℝ → ℝ
hf : ∀ (x y : ℝ), f (x + y) ≤ y * f x + f (f x)
⊢ ∀ x ≤ 0, f x = 0
"""

math2="""f : ℝ → ℝ
hf : ∀ (x y : ℝ), f (x + y) ≤ y * f x + f (f x)
hxt : ∀ (x t : ℝ), f t ≤ t * f x - x * f x + f (f x)
⊢ ∀ x ≤ 0, f x = 0
"""

a1 = AtomizedText(math1)
a2 = AtomizedText(math2, location=(0,-8,0))
