import bpy
import os

# k is a continuation to apply to envVar if it is defined
def envDefault(envVar, defaultVal, k = None):
  envVal = os.getenv(envVar)
  if k is None:
    return envVal or defaultVal
  else:
    return k(envVal) if envVal else defaultVal

def set_camera_view():
    for area in bpy.context.screen.areas:
        if area.type == 'VIEW_3D':
            area.spaces[0].region_3d.view_perspective = 'CAMERA'
            break

# got this from
# https://blender.stackexchange.com/questions/104651/selecting-gpu-with-python-script
def use_cycles_with_gpu():
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

    bpy.context.scene.cycles.feature_set = 'EXPERIMENTAL'
    bpy.context.scene.cycles.dicing_rate = 0.25


def set_render_engine_from_env(default="WORKBENCH"):
  v = os.getenv("RENDER_ENGINE", default=default)
  if v == "CYCLES":
    use_cycles_with_gpu()
  elif v == "EEVEE":
    bpy.data.scenes[0].render.engine = "BLENDER_EEVEE"
  elif v == "WORKBENCH":
    bpy.data.scenes[0].render.engine = "BLENDER_WORKBENCH"
    bpy.context.scene.display.shading.light = 'FLAT'
    bpy.context.scene.view_settings.view_transform = 'Standard'
  else:
    raise Exception("unknown render engine " + v)

def import_svg(filepath, scale=100, location=(0,0,0), parent=None):
  collections_before = set()
  for c in bpy.data.collections:
    collections_before.add(c.name)

  bpy.ops.import_curve.svg(filepath=filepath)
  svg_collection = None
  for c in bpy.data.collections:
    if not (c.name in collections_before):
      svg_collection = c

  for obj in svg_collection.objects:
    obj.scale = (scale,scale,scale)
    obj.location = location
    obj.parent = parent
