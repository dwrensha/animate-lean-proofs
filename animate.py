
from dataclasses import dataclass
import os
import bpy

import sys
sys.path.append(os.getcwd())
import common

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
            cursor += len(e.text)
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
            cursor += len(t)
        else :
            raise Exception("unknown edit type: {}".format(e))
    return string

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

RESOLUTION_X = 1920
RESOLUTION_Y = 1080
FPS = 60
bpy.context.scene.render.resolution_x = RESOLUTION_X
bpy.context.scene.render.resolution_y = RESOLUTION_Y
bpy.context.scene.render.fps = FPS
bpy.context.scene.frame_start = 0
bpy.context.scene.frame_end = 300

CAMERA = bpy.data.objects["Camera"]
CAMERA.data.type = "ORTHO"
CAMERA.data.ortho_scale = 23

CAMERA.location = (12, -1.5, 1)
CAMERA.rotation_euler  = (0,0,0)

# delete the default cube
if "Cube" in bpy.data.objects:
    bpy.data.objects['Cube'].select_set(True)
    bpy.context.view_layer.objects.active = bpy.data.objects['Cube']
    bpy.ops.object.delete()

#MONOFONTPATH = "/home/dwrensha/fonts/JuliaMono-Regular.ttf"
MONOFONTPATH = "/home/dwrensha/fonts/DejaVuSansMono.ttf"
MONOFONT = bpy.data.fonts.load(MONOFONTPATH)

PANEL_MATERIAL = bpy.data.materials.new(name="Panel")
PANEL_MATERIAL.diffuse_color = (0.012, 0.045, 0.117, 1)

PANEL_BORDER_COLOR = (0.005, 0.02, 0.05, 1)
PANEL_BORDER_PROVED_COLOR = (0.005, 0.4, 0.1, 1)

TEXT_MATERIAL = bpy.data.materials.new(name="TextMaterial")
TEXT_MATERIAL.diffuse_color = (1, 1, 1, 1)

@dataclass
class CharObj:
    c: str
    obj: object

def get_font_dimensions():
    bpy.ops.object.text_add()
    cobj = bpy.context.object
    cobj.data.body = "M"
    cobj.data.font = MONOFONT
    bpy.context.view_layer.update()
    dims = cobj.dimensions
    bpy.ops.object.delete()
    return dims

class Goal:
    def __init__(self, string, title=None, edits = [], location = (0,0,0)):
        dims = get_font_dimensions()
        self.char_width=dims.x
        self.char_height=dims.y
        self.line_height = self.char_height * 1.8

        self.margin = 0.25
        bpy.ops.object.empty_add(location=location)
        self.top = bpy.context.object
        self.top.name = "Goal"

        if title:
            title_scale = 0.75
            bpy.ops.object.text_add()
            self.title = bpy.context.object
            self.title.scale=(title_scale, title_scale, title_scale)
            self.title.data.body = title
            self.title.data.font = MONOFONT
            height = self.title.dimensions.y
            self.title_height = height * 1.5
            self.title.location = (self.margin, -height * 1.25, 0)

            self.title.parent = self.top
        else:
            self.title_height = 0
            self.title = None

        self.panel_border_material = bpy.data.materials.new(name="PanelBorder")
        self.panel_border_material.diffuse_color = PANEL_BORDER_COLOR

        bpy.ops.mesh.primitive_plane_add()
        self.panel_border = bpy.context.object
        self.panel_border.parent = self.top
        self.panel_border.data.materials.append(self.panel_border_material)

        bpy.ops.object.empty_add(
            location=(self.margin, -self.margin - self.title_height, 0))
        self.inner = bpy.context.object
        self.inner.name = "Inner"
        self.inner.parent = self.top

        bpy.ops.mesh.primitive_plane_add()
        self.panel = bpy.context.object
        self.panel.parent = self.inner
        self.panel.data.materials.append(PANEL_MATERIAL)


        self.objs = []
        self.all_objs = []
        self.cursor = 0
        self.clipboard = []

        for c in string:
            self.objs.append(self.new_char_obj(c))

        # snapshots of self.objs
        self.keyframes = [self.objs]

    def center_camera(self, frame):
        bpy.context.scene.frame_set(frame)
        dims = self.panel_border.dimensions
        center = self.panel_border.matrix_world.translation
        CAMERA.location = (center.x, center.y, 1)
        CAMERA.keyframe_insert(data_path="location", index=-1, frame=frame)
        CAMERA.data.ortho_scale = dims.x * 1.2
        CAMERA.data.keyframe_insert(data_path="ortho_scale", index=-1, frame=frame)

    def lay_out(self, idx):
        for obj in self.all_objs:
            if obj.obj:
                obj.obj.scale = (0,0,0)

        xidx = 0
        yidx = 0
        max_row_idx = 0
        for obj in self.keyframes[idx]:
            if obj.c == "\n":
                if xidx > max_row_idx:
                    max_row_idx = xidx
                yidx += 1
                xidx = 0
                continue
            if obj.obj:
                obj.obj.location = self.to_location(xidx, yidx)
                obj.obj.scale = (1,1,1)
            xidx += 1

        width = max_row_idx * self.char_width + 2 * self.margin
        if self.title and self.title.dimensions.x > width:
            width = self.title.dimensions.x

        height = yidx * self.line_height + 2 * self.margin
        self.panel.scale = (width/2,height/2,1)
        self.panel.location=(width/2,- height/2,-0.05)

        border_height = height + self.title_height + 2 * self.margin
        self.panel_border.scale = (width/2 + self.margin, border_height / 2, 1)
        self.panel_border.location=(width/2 + self.margin,-border_height / 2,-0.06)


    def set_keyframe(self, idx, frame, center_camera=True):
        bpy.context.scene.frame_set(frame)
        self.lay_out(idx)
        for obj in self.all_objs:
            if obj.obj:
                obj.obj.keyframe_insert(data_path="location", index=-1, frame=frame)
                obj.obj.keyframe_insert(data_path="scale", index=-1, frame=frame)
        self.panel.keyframe_insert(data_path="scale", index=-1, frame=frame)
        self.panel.keyframe_insert(data_path="location", index=-1, frame=frame)
        self.panel_border.keyframe_insert(data_path="scale", index=-1, frame=frame)
        self.panel_border.keyframe_insert(data_path="location", index=-1, frame=frame)
        if center_camera:
            self.center_camera(frame)

    def new_char_obj(self, c):
        if c.isspace():
            cobj = None
        else:
            bpy.ops.object.text_add(scale=(0,0,0))
            cobj = bpy.context.object
            cobj.data.body = c
            cobj.parent = self.inner
            cobj.data.font = MONOFONT
            cobj.data.materials.append(TEXT_MATERIAL)
        result = CharObj(c, cobj)
        self.all_objs.append(result)
        return result

    def to_location(self, xidx, yidx):
        return (self.margin + xidx * self.char_width,
                (- self.char_height) +
                (yidx * self.line_height) * -1 - self.margin,
                0)

    def apply_edits(self, edits):
        for e in edits:
            if type(e) is MoveCursor:
                self.cursor += e.offset
                assert(0 <= self.cursor)
                assert(self.cursor <= len(self.objs))
            elif type(e) is Insert:
                new_objs = []
                for c in e.text:
                    new_objs.append(self.new_char_obj(c))
                self.objs = self.objs[:self.cursor] + new_objs + self.objs[self.cursor:]
                self.cursor += len(new_objs)
            elif type(e) is Delete:
                assert(self.cursor + e.length <= len(self.objs))
                self.objs = self.objs[:self.cursor] + self.objs[self.cursor + e.length:]
            elif type(e) is Cut:
                assert(self.cursor + e.length <= len(self.objs))
                self.clipboard.append(self.objs[self.cursor:self.cursor + e.length])
                self.objs = self.objs[:self.cursor] + self.objs[self.cursor + e.length:]
            elif type(e) is Paste:
                t = self.clipboard.pop()
                self.objs = self.objs[:self.cursor] + t + self.objs[self.cursor:]
                self.cursor += len(t)
            else :
                raise Exception("unknown edit type: {}".format(e))

        self.keyframes.append(self.objs)
        self.lay_out(len(self.keyframes)-1)

    def to_text(self):
        text = ""
        for obj in self.objs:
            text += obj.c
        return text

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
x t : ℝ
⊢ f t ≤ t * f x - x * f x + f (f x)
"""

edits = [MoveCursor(63), Cut(7), MoveCursor(-3), Delete(6),
         MoveCursor(-2), Paste(), Insert("\n")]
math2_ = apply_edits(edits, math2)
assert(math2_ == math3)

math4="""f : ℝ → ℝ
hf : ∀ (x t : ℝ), f t ≤ t * f x - x * f x + f (f x)
⊢ ∀ x ≤ 0, f x = 0
"""

a1 = Goal(math1, title="Main Goal")
a1.apply_edits([])
a1.set_keyframe(1, 0)

a2 = Goal(math2,
          title="replace hf : ∀ (x t : ℝ), f t ≤ t * f x - x * f x + f (f x)",
          #title="have hxt",
          location=(0,-6,0))
#a3 = Goal(math3, location=(0,-12,0))
print(a2.to_text())
a2.apply_edits(edits)
print(a2.to_text())


edits2 = [MoveCursor(2), Delete(3), Insert("f (x + (t - x))")]
a2.apply_edits(edits2)
print(a2.to_text())

a2.apply_edits([])

edits3 = [MoveCursor(-15), Delete(15), Insert("(t - x) * f x + f (f x)")]
a2.apply_edits(edits3)
print(a2.to_text())

a2.apply_edits([])

edits4 = [MoveCursor(-23), Delete(13), Insert("t * f x - x * f x")]
a2.apply_edits(edits4)

a2.apply_edits([])
a2.apply_edits([MoveCursor(11), Delete(1), Insert("=")])
print(a2.to_text())


a2.set_keyframe(0, 30)
a2.set_keyframe(1, 60)
a2.set_keyframe(2, 90)
a2.set_keyframe(3, 120)
a2.set_keyframe(4, 150)
a2.set_keyframe(5, 180)
a2.set_keyframe(6, 210)
a2.set_keyframe(7, 240)
a2.set_keyframe(8, 270)

common.set_camera_view()
