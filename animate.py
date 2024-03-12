
from dataclasses import dataclass, field
import os
from pathlib import Path
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
class DeleteAll:
    pass

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
        elif type(e) is DeleteAll:
            string = ""
            cursor = 0
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
bpy.context.scene.render.filepath = common.envDefault("OUTDIR", "/tmp/out")

FPS = common.envDefault("FPS", 60, int)
bpy.context.scene.render.resolution_x = common.envDefault("RESOLUTION_X", 1920, int)
bpy.context.scene.render.resolution_y = common.envDefault("RESOLUTION_Y", 1080, int)
bpy.context.scene.render.fps = FPS
bpy.context.scene.frame_start = common.envDefault("FRAME_START", 0, int)

CAMERA = bpy.data.objects["Camera"]
CAMERA.data.type = "ORTHO"
CAMERA.data.ortho_scale = 23

CAMERA.location = (12, -1.5, 1)
CAMERA.rotation_euler  = (0,0,0)
common.set_camera_view()

# delete the default cube
if "Cube" in bpy.data.objects:
    bpy.data.objects['Cube'].select_set(True)
    bpy.context.view_layer.objects.active = bpy.data.objects['Cube']
    bpy.ops.object.delete()

FONTDIR = common.envDefault("FONTDIR", Path.home() / "fonts", Path)
#MONOFONTPATH = str(FONTDIR / "JuliaMono-Regular.ttf")
MONOFONTPATH = str(FONTDIR / "DejaVuSansMono.ttf")
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

    def keyframe_insert(self, frame):
        if self.obj:
            self.obj.keyframe_insert(data_path="location", index=-1, frame=frame)
            self.obj.keyframe_insert(data_path="scale", index=-1, frame=frame)

def get_font_dimensions():
    bpy.ops.object.text_add()
    cobj = bpy.context.object
    cobj.data.body = "M"
    cobj.data.font = MONOFONT
    bpy.context.view_layer.update()
    dims = cobj.dimensions
    bpy.ops.object.delete()
    return dims

@dataclass
class GoalStep:
    # CharObjs that are displayed in this step
    objs: list[CharObj] = field(default_factory=list)

    cursor: int = 0

    start_frame: int = 0
    end_frame: int = 0

    # newly created CharObjs
    new_objs: list[CharObj] = field(default_factory=list)

    # newly deleted CharObjs
    deleted_objs: list[CharObj] = field(default_factory=list)

class Goal:
    def __init__(self, string, title=None, start_frame = 0,
                 edits = [], location = (0,0,0)):
        self.start_frame = start_frame
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

        gs = GoalStep()
        gs.start_frame = start_frame
        gs.end_frame = start_frame
        for c in string:
            obj = self.new_char_obj(c)
            gs.objs.append(obj)
            #kj.new_objs.append(obj)

        self.goalsteps = [gs]
        self.set_keyframe(gs)

    def latest_frame(self):
        if len(self.goalsteps) > 0:
            return self.goalsteps[-1].end_frame
        else:
            return self.start_frame

    def duration(self):
        return self.latest_frame() - self.start_frame

    def center_camera(self, frame):
        dims = self.panel_border.dimensions
        center = self.panel_border.matrix_world.translation
        CAMERA.location = (center.x, center.y, 1)
        CAMERA.keyframe_insert(data_path="location", index=-1, frame=frame)
        CAMERA.data.ortho_scale = dims.x * 1.2
        CAMERA.data.keyframe_insert(data_path="ortho_scale", index=-1, frame=frame)

    def lay_out(self, gs):
        xidx = 0
        yidx = 0
        max_row_idx = 0
        for obj in gs.objs:
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
        height = yidx * self.line_height + 2 * self.margin

        if len(gs.objs) == 0:
            width = 0
            height = 0

        for obj in gs.deleted_objs:
            if obj.obj:
                obj.obj.scale = (0,0,0)

        if self.title and self.title.dimensions.x > width:
            width = self.title.dimensions.x

        self.panel.scale = (width/2,height/2,1)
        self.panel.location=(width/2,- height/2,-0.05)

        border_height = height + self.title_height + 2 * self.margin
        self.panel_border.scale = (width/2 + self.margin, border_height / 2, 1)
        self.panel_border.location=(width/2 + self.margin,-border_height / 2,-0.06)
        bpy.context.view_layer.update()

    def set_keyframe(self, gs, center_camera=True):
        self.lay_out(gs)
        for obj in gs.new_objs:
            if obj.obj:
                obj.obj.scale = (0,0,0)
                obj.keyframe_insert(gs.start_frame)
                obj.obj.scale = (1,1,1)

        for obj in gs.objs:
            obj.keyframe_insert(gs.end_frame)

        for obj in gs.deleted_objs:
            obj.keyframe_insert(gs.end_frame)

        self.panel.keyframe_insert(data_path="location", index=-1, frame=gs.end_frame)
        self.panel.keyframe_insert(data_path="scale", index=-1, frame=gs.end_frame)
        self.panel.keyframe_insert(data_path="location", index=-1, frame=gs.end_frame)
        self.panel_border.keyframe_insert(data_path="scale", index=-1, frame=gs.end_frame)
        self.panel_border.keyframe_insert(data_path="location", index=-1,
                                          frame=gs.end_frame)
        if center_camera:
            self.center_camera(gs.end_frame)

    def appear(self, frame):
        if frame > 0:
            self.top.scale = (0,0,0)
            self.top.keyframe_insert(data_path="scale", index=-1, frame= frame - 1)

        self.top.scale = (1,1,1)
        self.top.keyframe_insert(data_path="scale", index=-1, frame= frame)

    def shrink_to_nothing(self, start_frame, end_frame):
        self.top.scale = (1,1,1)
        self.top.keyframe_insert(data_path="scale", index=-1, frame= start_frame)

        self.top.scale = (0,0,0)
        self.top.keyframe_insert(data_path="scale", index=-1, frame= end_frame)

    def fade_border_color(self, start_frame, end_frame, start_color, end_color):
        self.panel_border_material.diffuse_color = start_color
        self.panel_border_material.keyframe_insert(
            data_path="diffuse_color", index=-1, frame=start_frame)
        self.panel_border_material.diffuse_color = PANEL_BORDER_PROVED_COLOR
        self.panel_border_material.keyframe_insert(
            data_path="diffuse_color", index=-1, frame=end_frame)

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
        return result

    def to_location(self, xidx, yidx):
        return (self.margin + xidx * self.char_width,
                (- self.char_height) +
                (yidx * self.line_height) * -1 - self.margin,
                0)

    # duration is a frame count
    def add_edits(self, duration, edits,
                  center_camera = True):
        gs = GoalStep()
        if len(self.goalsteps) > 0:
            gs.objs = self.goalsteps[-1].objs.copy()
            gs.cursor = self.goalsteps[-1].cursor
        gs.start_frame = self.latest_frame()
        gs.end_frame = gs.start_frame + duration

        if gs.end_frame > bpy.context.scene.frame_end:
            bpy.context.scene.frame_end = gs.end_frame

        clipboard = []
        for e in edits:
            if type(e) is MoveCursor:
                gs.cursor += e.offset
                assert(0 <= gs.cursor)
                assert(gs.cursor <= len(gs.objs))
            elif type(e) is Insert:
                for c in e.text:
                    gs.new_objs.append(self.new_char_obj(c))
                gs.objs = gs.objs[:gs.cursor] + gs.new_objs + gs.objs[gs.cursor:]
                gs.cursor += len(gs.new_objs)
            elif type(e) is Delete:
                assert(gs.cursor + e.length <= len(gs.objs))
                gs.deleted_objs = gs.objs[gs.cursor:gs.cursor + e.length]
                gs.objs = gs.objs[:gs.cursor] + gs.objs[gs.cursor + e.length:]
            elif type(e) is DeleteAll:
                gs.deleted_objs = gs.objs.copy()
                gs.objs = []
                gs.cursor = 0
            elif type(e) is Cut:
                assert(gs.cursor + e.length <= len(gs.objs))
                clipboard.append(gs.objs[gs.cursor:gs.cursor + e.length])
                gs.objs = gs.objs[:gs.cursor] + gs.objs[gs.cursor + e.length:]
            elif type(e) is Paste:
                t = clipboard.pop()
                gs.objs = gs.objs[:gs.cursor] + t + gs.objs[gs.cursor:]
                gs.cursor += len(t)
            else :
                raise Exception("unknown edit type: {}".format(e))

        assert(len(clipboard) == 0)
        self.goalsteps.append(gs)
        self.set_keyframe(self.goalsteps[-1], center_camera = center_camera)

    def wait(self, duration):
        self.add_edits(duration, [])

    def to_text(self):
        text = ""
        for obj in self.goalsteps[-1].objs:
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

edits = [MoveCursor(63), Cut(7), MoveCursor(-3), Delete(6),
         MoveCursor(-2), Paste(), Insert("\n")]
math2_ = apply_edits(edits, math2)
assert(math2_ == """f : ℝ → ℝ
hf : ∀ (x y : ℝ), f (x + y) ≤ y * f x + f (f x)
x t : ℝ
⊢ f t ≤ t * f x - x * f x + f (f x)
""")

a1 = Goal(math1, title="Main Goal")
a1.wait(30)

a2 = Goal(math2,
          title="replace hf : ∀ (x t : ℝ), f t ≤ t * f x - x * f x + f (f x)",
          start_frame=a1.latest_frame(),
          location=(0,-5,0))
a2.appear(a1.latest_frame())
print(a2.to_text())
a2.wait(30)
a2.add_edits(30, edits)
#print(a2.to_text())

a2.wait(30)
a2.add_edits(30, [MoveCursor(2), Delete(3), Insert("f (x + (t - x))")])
#print(a2.to_text())

a2.wait(30)

edits3 = [MoveCursor(-15), Delete(15), Insert("(t - x) * f x + f (f x)")]
a2.add_edits(30, edits3)
#print(a2.to_text())

a2.wait(30)

edits4 = [MoveCursor(-23), Delete(13), Insert("t * f x - x * f x")]
a2.add_edits(30, edits4)

a2.wait(30)
a2.add_edits(30, [MoveCursor(11), Delete(1), Insert("=")])
#print(a2.to_text())

a2.wait(30)
a2.add_edits(30, [DeleteAll()])
a2.fade_border_color(a2.latest_frame() - 30, a2.latest_frame(),
                     PANEL_BORDER_COLOR, PANEL_BORDER_PROVED_COLOR)
a2.wait(30)
a2.shrink_to_nothing(a2.latest_frame(), a2.latest_frame() + 30)

#print(a2.to_text())

a1.add_edits(a2.duration(), [], center_camera=False)
a1.add_edits(
    30,
    [MoveCursor(15), Delete(42), Insert("∀ (x t : ℝ), f t ≤ t * f x - x * f x + f (f x)")])
a1.wait(30)
a1.wait(30)

math3="""f : ℝ → ℝ
hf : ∀ (x t : ℝ), f t ≤ t * f x - x * f x + f (f x)
⊢ ∀ (a b : ℝ), a * f a + b * f b ≤ 2 * f a * f b
"""

a3 = Goal(math3,
          title = "have hab : ∀ a b, a * f a + b * f b ≤ 2 * f a * f b",
          start_frame = a1.latest_frame(),
          location=(0,-5,0))
a3.appear(a1.latest_frame())
a3.wait(30)

if os.getenv("FRAME_END"):
    bpy.context.scene.frame_end = int(os.getenv("FRAME_END"))
if os.getenv("RENDER"):
    bpy.ops.render.render(animation=True, write_still=True, use_viewport=False, layer='', scene='')
if os.getenv("SAVETO"):
    bpy.ops.wm.save_as_mainfile(filepath=os.getenv("SAVETO"))
