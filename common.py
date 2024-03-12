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
