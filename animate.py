from dataclasses import dataclass
import os
import bpy


@dataclass
class MoveCursor:
    offset: int

@dataclass
class Insert:
    text: str

@dataclass
class Delete:
    length: int = 1

@dataclass
class Cut:
    length: int

@dataclass
class Paste:
    pass

def apply_edits(edits, string):
    cursor = 0
    clipboard = []
    for e in edits:
        if type(e) is MoveCursor:
            cursor += e.offset
            assert(0 <= cursor)
            assert(cursor <= len(string))
        elif type(e) is Insert:
            string = string[:cursor] + e.text + string[cursor:]
        elif type(e) is Delete:
            assert(cursor + e.length <= len(string))
            string = string[:cursor] + string[cursor + e.length:]
        elif type(e) is Cut:
            assert(cursor + e.length <= len(string))
            clipboard.append(string[cursor:cursor + e.length])
            string = string[:cursor] + string[cursor + e.length:]
        elif type(e) is Paste:
            t = clipboard.pop()
            string = string[:cursor] + t + string[cursor:]
        else :
            raise Exception("unknown edit type: {}".format(e))
    return string

edits = [MoveCursor(2), Insert("ABC"), Delete(), MoveCursor(-2), Cut(2), MoveCursor(5), Paste(), Delete(1)]
print(apply_edits(edits, "hello"))

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

bpy.context.scene.render.filepath = "/tmp/out"

bpy.context.scene.render.resolution_x = 1920
bpy.context.scene.render.resolution_y = 1080


CAMERA = bpy.data.objects["Camera"]
CAMERA.data.type = "ORTHO"
CAMERA.data.ortho_scale = 20

CAMERA.location = (6, 0, 1)
CAMERA.rotation_euler  = (0,0,0)

# delete the default cube
if "Cube" in bpy.data.objects:
    bpy.data.objects['Cube'].select_set(True)
    bpy.context.view_layer.objects.active = bpy.data.objects['Cube']
    bpy.ops.object.delete()

#FONTPATH = "/home/dwrensha/fonts/DejaVuSansCondensed.ttf"
MONOFONTPATH = "/home/dwrensha/fonts/DejaVuSansMono.ttf"
MONOFONT = bpy.data.fonts.load(MONOFONTPATH)

PANEL_MATERIAL = bpy.data.materials.new(name="Panel")
PANEL_MATERIAL.diffuse_color = (0.012, 0.045, 0.117, 1)

TEXT_MATERIAL = bpy.data.materials.new(name="TextMaterial")
TEXT_MATERIAL.diffuse_color = (1, 1, 1, 1)

class Goal:
    def __init__(self, string, location = (0,0,0)):
        bpy.ops.object.text_add()
        cobj = bpy.context.object
        cobj.data.body = "M"
        cobj.data.font = MONOFONT
        bpy.context.view_layer.update()
        self.margin = 0.25
        self.char_width=cobj.dimensions.x
        self.char_height=cobj.dimensions.y
        self.line_height = self.char_height * 1.8
        bpy.ops.object.delete()

        bpy.ops.object.empty_add(location=location)
        self.top = bpy.context.object
        self.top.name = "Goal"
        yidx = 0
        max_row_idx = 0
        for line in string.splitlines():
            xidx = 0

            for c in line:
                bpy.ops.object.text_add(
                    location = self.to_location(xidx, yidx))
                cobj = bpy.context.object
                cobj.data.body = c
                cobj.parent = self.top
                xidx += 1
                cobj.data.font = MONOFONT
                cobj.data.materials.append(TEXT_MATERIAL)

            if xidx > max_row_idx:
                max_row_idx = xidx
            yidx += 1

        width = max_row_idx * self.char_width + 2 * self.margin
        height = yidx * self.line_height + 2 * self.margin
        bpy.ops.mesh.primitive_plane_add(
            location=(width/2,- height/2,-0.05))
        self.panel = bpy.context.object
        self.panel.parent = self.top
        self.panel.scale = (width/2,height/2,1)
        self.panel.data.materials.append(PANEL_MATERIAL)

    def to_location(self, xidx, yidx):
        return (self.margin + xidx * self.char_width,
                (- self.char_height) +
                (yidx * self.line_height) * -1 - self.margin,
                0)

#bpy.ops.object.text_add(
#    enter_editmode=False, align='WORLD', location=(0, 0, 0), scale=(1, 1, 1))
#bpy.context.object.name = "Math1"

math1 = """f : ℝ → ℝ
hf : ∀ (x y : ℝ), f (x + y) ≤ y * f x + f (f x)
⊢ ∀ x ≤ 0, f x = 0
"""

math2="""f : ℝ → ℝ
hf : ∀ (x y : ℝ), f (x + y) ≤ y * f x + f (f x)
⊢ ∀ (x t : ℝ), f t ≤ t * f x - x * f x + f (f x)
"""

math3="""f : ℝ → ℝ
hf : ∀ (x y : ℝ), f (x + y) ≤ y * f x + f (f x)
hxt : ∀ (x t : ℝ), f t ≤ t * f x - x * f x + f (f x)
⊢ ∀ x ≤ 0, f x = 0
"""

a1 = Goal(math1)
a2 = Goal(math2, location=(0,-8,0))
