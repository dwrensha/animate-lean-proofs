import argparse
from dataclasses import dataclass, field
from typing import Tuple
import json
import math
import os
from pathlib import Path
import sys
import bpy

import sys
sys.path.append(os.getcwd())
import common

common.set_render_engine_from_env()
bpy.context.scene.render.image_settings.file_format = 'FFMPEG'
FPS = common.envDefault("FPS", 60, int)
RESOLUTION_X = 1920
RESOLUTION_Y = 1080
bpy.context.scene.render.resolution_x = common.envDefault("RESOLUTION_X", RESOLUTION_X, int)
bpy.context.scene.render.resolution_y = common.envDefault("RESOLUTION_Y", RESOLUTION_Y, int)
bpy.context.scene.render.fps = FPS
bpy.context.scene.frame_start = common.envDefault("FRAME_START", 0, int)

CAMERA = bpy.data.objects["Camera"]
CAMERA.data.type = "ORTHO"
CAMERA.data.ortho_scale = 23

FOREGROUND_PANEL_Z = 10
CAMERA_Z = 12
CAMERA.location = (12, -1.5, CAMERA_Z)
CAMERA.rotation_euler  = (0,0,0)
common.set_camera_view()

# delete the default cube
if "Cube" in bpy.data.objects:
    bpy.data.objects['Cube'].select_set(True)
    bpy.context.view_layer.objects.active = bpy.data.objects['Cube']
    bpy.ops.object.delete()

TADA_FILEPATH = "assets/tada.svg"

FONTDIR = common.envDefault("FONTDIR", Path.home() / "fonts", Path)

#MONOFONTPATH = str(FONTDIR / "DejaVuSansMono.ttf")
# JuliaMono one looks better for chess
MONOFONTPATH = str(FONTDIR / "JuliaMono-Regular.ttf")

MONOFONT = bpy.data.fonts.load(MONOFONTPATH)

# background color
bpy.context.scene.world.color = (0.1, 0.16, 0.22)

PANEL_COLOR = (0.012, 0.012, 0.01, 1)

PANEL_BORDER_COLOR = (0.005, 0.02, 0.05, 1)
PANEL_BORDER_PROVED_COLOR = (0.005, 0.4, 0.1, 1)

TEXT_MATERIAL = bpy.data.materials.new(name="TextMaterial")
TEXT_MATERIAL.diffuse_color = (1, 1, 1, 1)

FOREGROUND_PANEL_COLOR = (0.01, 0.01, 0.01, 1)

HIGHLIGHT_COLOR = (1.0, 0.96, 0.3, 1)
HIGHLIGHT_COLOR_TRANSPARENT = (1.0, 0.96, 0.3, 0)

SYNTAX_CATS = {
    0 : "Token.Text",
    1 : "Token.Text",
    2 : "Token.Text.Whitespace",
    3 : "Token.Keyword",
    4 : "Token.Name",
    5 : "Token.Name.Builtin.Pseudo",
    6 : "Token.Operator",
    7 : "Token.Literal.Number.Integer",
}

def rgba_of_hex(h):
    h = h.lstrip('#')
    return (int(h[0:2], 16) / 255,
            int(h[2:4], 16) / 255,
            int(h[4:6], 16) / 255,
            1.0)

@dataclass
class CharObj:
    c: str
    obj: object

    def keyframe_insert(self, frame):
        if self.obj:
            self.obj.keyframe_insert(data_path="location", index=-1, frame=frame)
            self.obj.keyframe_insert(data_path="scale", index=-1, frame=frame)
            self.obj.data.materials[0].keyframe_insert(data_path="diffuse_color", index=-1, frame=frame)

def get_font_dimensions():
    bpy.ops.object.text_add()
    cobj = bpy.context.object
    cobj.data.body = "M"
    cobj.data.font = MONOFONT
    bpy.context.view_layer.update()
    (x,y,z) = cobj.dimensions
    bpy.ops.object.delete()
    return (x * 1.25, y)

@dataclass
class GoalStep:
    # the mvarId of the goal after this step
    goalId: str = field(default_factory=str)

    goal_json: dict = field(default_factory=dict)

    # string goal state after this step
    state: str = field(default_factory=str)

    # CharObjs that are displayed in the body after this step
    objs: list[CharObj] = field(default_factory=list)

    start_frame: int = 0
    end_frame: int = 0

    # newly created CharObjs
    new_objs: list[CharObj] = field(default_factory=list)

    # newly deleted CharObjs
    deleted_objs: list[CharObj] = field(default_factory=list)

    # Width of Goal after this GoalStep applies. Populated by lay_out().
    width: float = 0

    # Height of Goal after this GoalStep applies. Populated by lay_out().
    height: float = 0

    # World location of the goal's upper left corner after this GoalStep applies.
    # Populated by set_last_location().
    location: Tuple[float, float, float] = (0,0,0)

class Goal:
    def __init__(self,
                 world,
                 new_goal_json,
                 appear_frame_count = 5,
                 location = (0,0,0)):
        self.world = world
        self.id = new_goal_json['goalId']
        self.goal_steps = []

        start_frame = world.current_frame

        self.char_width, self.char_height = get_font_dimensions()
        self.line_height = self.char_height * 1.63
        self.margin = 0.25

        bpy.ops.object.empty_add()
        self.top = bpy.context.object
        self.top.name = "Goal"

        self.panel_material = bpy.data.materials.new(name="Panel")
        self.panel_material.diffuse_color = PANEL_COLOR

        bpy.ops.mesh.primitive_plane_add()
        self.panel = bpy.context.object
        self.panel.parent = self.top
        self.panel.data.materials.append(self.panel_material)
        self.panel.scale = (0,0,1)
        self.panel.location = (0,0,-0.05)

        self.highlight_panel_material = bpy.data.materials.new(name="Highlight Panel")
        self.highlight_panel_material.diffuse_color = HIGHLIGHT_COLOR
        bpy.ops.mesh.primitive_plane_add()
        self.highlight_panel = bpy.context.object
        self.highlight_panel.parent = self.top
        self.highlight_panel.data.materials.append(self.highlight_panel_material)
        self.highlight_panel.scale = (0,0,1)
        self.highlight_panel.location = (0,0,-0.05)

        self.add_panel_keyframe(start_frame)

        gs = GoalStep()
        gs.goalId = new_goal_json['goalId']
        gs.goal_json = new_goal_json
        gs.start_frame = start_frame
        gs.end_frame = start_frame + appear_frame_count
        gs.state = new_goal_json['state']
        for c in gs.state:
            obj = self.new_char_obj(c, parent=self.top)
            gs.objs.append(obj)
            gs.new_objs.append(obj)

        self.add_goalstep(gs)
        self.set_last_location(location)

    def __repr__(self):
        return "<{}>".format(self.id)

    def set_last_location(self, location,
                          frame = None):
        if frame is None:
            frame=self.last_frame()
        self.last_step().location = location
        self.top.location = location
        self.top.keyframe_insert(data_path="location", index=-1, frame=frame)

    def to_location(self, xidx, yidx, scale_factor=1):
        return (self.margin + xidx * self.char_width * scale_factor,
                (- self.char_height * scale_factor) -
                 (yidx * self.line_height * scale_factor) - self.margin,
                0)

    def new_char_obj(self, c, scale = 1.0, parent=None):
        if c.isspace():
            cobj = None
        else:
            bpy.ops.object.text_add()
            cobj = bpy.context.object
            cmaterial = bpy.data.materials.new(name="CharMaterial")
            cmaterial.diffuse_color = (1, 1, 1, 1)
            cobj.data.materials.append(cmaterial)
            cobj.data.body = c
            cobj.data.font = MONOFONT
            bpy.ops.object.convert(target='MESH')
            cobj.parent = parent
            cobj.scale=(scale,scale,scale)

        result = CharObj(c, cobj)
        return result

    def lay_out(self, gs):
        # main body
        xidx = 0
        yidx = 0
        max_row_idx = 0
        for (idx, obj) in enumerate(gs.objs):
            if obj.c == "\n":
                yidx += 1
                xidx = 0
                continue
            if obj.obj:
                obj.obj.location = self.to_location(xidx, yidx)
                obj.obj.scale = (1,1,1)
                color = self.world.get_color_of_char(gs.goalId, idx)
                obj.obj.data.materials[0].diffuse_color = color
            xidx += 1
            if xidx > max_row_idx:
                max_row_idx = xidx

        # get correct line count even if we didn't end with a newline
        if xidx != 0:
            yidx += 1

        width = max_row_idx * self.char_width + 2 * self.margin
        height = yidx * self.line_height + 2 * self.margin

        if len(gs.objs) == 0:
            width = 0
            height = 0

        for obj in gs.deleted_objs:
            if obj.obj:
                obj.obj.scale = (0,0,0)

        self.panel.scale = (width/2,height/2,1)
        self.panel.location = (width/2,-height/2,-0.05)

        highlight_margin = 0.09
        self.highlight_panel.scale = (width/2 + highlight_margin,
                                      height/2 + highlight_margin,
                                      1)
        self.highlight_panel.location = (width/2,-height/2,-0.06)

        gs.width = width
        gs.height = height

    def add_panel_keyframe(self, frame):
        self.panel.keyframe_insert(data_path="location", index=-1, frame=frame)
        self.panel.keyframe_insert(data_path="scale", index=-1, frame=frame)
        self.highlight_panel.keyframe_insert(data_path="location", index=-1, frame=frame)
        self.highlight_panel.keyframe_insert(data_path="scale", index=-1, frame=frame)

    def add_highlighting_keyframe(self, frame, color):
        self.highlight_panel_material.diffuse_color = color
        self.highlight_panel_material.keyframe_insert(data_path="diffuse_color", index=-1, frame=frame)

    def add_goalstep(self, gs, highlight=False):
        if highlight:
            self.add_highlighting_keyframe(gs.start_frame + 1, HIGHLIGHT_COLOR)
        elif len(self.goal_steps) > 0:
            if not self.last_step().state == gs.state :
                self.add_highlighting_keyframe(gs.start_frame + 1, HIGHLIGHT_COLOR)
            else:
                self.add_highlighting_keyframe(gs.start_frame + 1, HIGHLIGHT_COLOR_TRANSPARENT)

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

        self.add_panel_keyframe(gs.end_frame)

        self.goal_steps.append(gs)
        if highlight:
            self.add_highlighting_keyframe(gs.end_frame, HIGHLIGHT_COLOR)
        else:
            self.add_highlighting_keyframe(gs.end_frame, HIGHLIGHT_COLOR_TRANSPARENT)

    def last_step(self):
        assert(len(self.goal_steps) > 0)
        return self.goal_steps[-1]

    def last_frame(self):
        return self.last_step().end_frame

    def last_goalId(self):
        return self.last_step().goalId

    def insert_wait_action(self, new_frame, highlight = False):
        last_step = self.last_step()
        gap_gs = GoalStep()
        gap_gs.goalId = last_step.goalId
        gap_gs.goal_json = last_step.goal_json
        gap_gs.state = last_step.state
        gap_gs.start_frame = last_step.end_frame
        gap_gs.end_frame = new_frame
        gap_gs.objs = last_step.objs.copy()
        self.add_goalstep(gap_gs, highlight = highlight)

    def add_action(self, s1, result_json,
                   frame_count = 60,
                   continue_from_last = False):
        g2 = result_json["goal"]
        s2 = g2["state"]
        last_step = self.last_step()
        if not s1 == last_step.state:
            raise Exception(
                "start state does not match previous end state\n{}\n vs \n{}".format(
                    s1, last_step.state))
        ims = result_json["indexMaps"]
        s1_to_s2 = ims["s1_to_s2"]
        s2_to_s1 = ims["s2_to_s1"]
        #if not(continue_from_last):
        #    self.insert_wait_action(self.world.current_frame)
        start_frame = self.last_frame()

        gs = GoalStep()
        gs.goalId = g2["goalId"]
        gs.goal_json = g2
        gs.state = s2
        gs.start_frame = start_frame
        gs.end_frame = gs.start_frame + frame_count
        for idx1, idx2 in enumerate(s1_to_s2):
            if idx2 is None:
                gs.deleted_objs.append(last_step.objs[idx1])
        for idx2, idx1 in enumerate(s2_to_s1):
            if idx1 is None:
                obj = self.new_char_obj(s2[idx2], parent = self.top)
                gs.new_objs.append(obj)
            else:
                obj = last_step.objs[idx1]
            gs.objs.append(obj)

        self.add_goalstep(gs)

    def add_done(self,
                 frame_count = 60):
        #if not(continue_from_last):
        #    self.insert_wait_action(self.world.current_frame)
        gs = GoalStep()
        gs.goalId = "[proved]"
        gs.state = ""
        gs.start_frame = self.last_frame()
        gs.end_frame = gs.start_frame + frame_count
        last_step = self.last_step()
        for obj in last_step.objs:
            gs.deleted_objs.append(obj)
        self.add_goalstep(gs)

def count_lines_and_columns(text):
    lines = text.split("\n")
    max_col = 0
    for line in lines:
        if len(line) > max_col:
            max_col = len(line)
    return (len(lines), max_col)

class TextAction:
    def __init__(self):
        pass

class SetText(TextAction):
    def __init__(self, new_text):
        self.new_text = new_text

    def act(self, world):
        world.set_foreground_text(self.new_text)

class ClearText(TextAction):
    def __init__(self):
        pass

    def act(self, world):
        world.foreground_text.data.body = ""
        world.goals_accomplished_text.data.body = ""
        world.tada.scale = (0,0,0)

class GoalsAccomplished(TextAction):
    def __init__(self):
        pass

    def act(self, world):
        world.goals_accomplished_text.data.body = "goals accomplished"
        world.tada.scale = (1,1,1)

class World:
    def __init__(self,
                 action_frame_count = 60,
                 wait_frame_count = 15,
                 switch_focus_frame_count = 30,
                 foreground_ratio_y = 0.2,
                 post_tactic_pause_frame_count = 4):
        self.action_frame_count = action_frame_count
        self.wait_frame_count = wait_frame_count
        self.switch_focus_frame_count = switch_focus_frame_count
        self.foreground_ratio_y = foreground_ratio_y
        self.post_tactic_pause_frame_count = post_tactic_pause_frame_count
        self.current_frame = 0

        self.char_width, self.char_height = get_font_dimensions()
        self.line_height = self.char_height * 2.2

        # list of active Goals, in reverse precedence order
        # goals later in the list get rendered higher in the animation
        self.goals = []

        # list of goals that have already been proved
        self.dead_goals = []

        bpy.ops.object.empty_add()
        self.foreground = bpy.context.object
        self.foreground.name = "Foreground"

        self.panel_material = bpy.data.materials.new(name="Foreground Panel")
        self.panel_material.diffuse_color = FOREGROUND_PANEL_COLOR

        bpy.ops.mesh.primitive_plane_add()
        self.panel = bpy.context.object
        self.panel.name = "panel"
        self.panel.parent = self.foreground
        self.panel.data.materials.append(self.panel_material)

        # in foreground coordinates, 1 = width of screen
        self.foreground_width = 1.0
        self.foreground_height = self.foreground_width / RESOLUTION_X * RESOLUTION_Y * self.foreground_ratio_y
        self.panel.scale = (self.foreground_width / 2, self.foreground_height / 2, 1)
        self.panel.location = (0,0,0)

        self.foreground_text_material = bpy.data.materials.new(
            name="ForegroundTextMaterial")
        self.foreground_text_material.diffuse_color = HIGHLIGHT_COLOR

        bpy.ops.object.text_add()
        self.foreground_text = bpy.context.object
        self.foreground_text.data.materials.append(self.foreground_text_material)
        self.foreground_text.data.body = ""
        self.foreground_text.data.font = MONOFONT
        #bpy.ops.object.convert(target='MESH')
        self.foreground_text.parent = self.foreground
        self.foreground_text.scale=(0, 0, 0)
        self.foreground_text.location=(-0.39,0.01,0.4)

        bpy.ops.object.text_add()
        self.goals_accomplished_text = bpy.context.object
        self.goals_accomplished_text.name = "Goals Accomplished"
        self.goals_accomplished_text.data.body = ""
        self.goals_accomplished_text.data.font = MONOFONT
        self.goals_accomplished_text.parent = self.foreground
        goals_accomplished_scale = 0.10
        self.goals_accomplished_text.scale = (goals_accomplished_scale,
                                              goals_accomplished_scale,
                                              goals_accomplished_scale)
        self.goals_accomplished_text.location = (-0.34, -0.28, 0.5)

        bpy.ops.object.empty_add()
        self.tada = bpy.context.object
        self.tada.name = "tada"
        self.tada.parent = self.foreground
        self.tada.scale = (0,0,0)
        common.import_svg(TADA_FILEPATH, scale=1.8, location = (0.326, -0.217, 0),
                          parent=self.tada)

        # list of (frame_number, TextAction)
        self.text_actions = [(0, ClearText())]

        bpy.app.handlers.frame_change_post.append(lambda s: self.post_frame(s))

    def init(self, movie_json):
        self.colors = dict()
        for r in movie_json["highlighting"]:
            k = r["goalId"]
            v = r["colors"]
            self.colors[k] = v

        self.add_goal(movie_json['startGoal'])
        actions = movie_json["actions"]
        for action in actions:
            self.add_action(action)

    def get_color_of_char(self, goalId, index):
        cat = SYNTAX_CATS[self.colors[goalId][index]]
        if cat == "Token.Text":
            return (1.0, 1.0, 1.0, 1.0)
        elif cat == "Token.Text.Whitespace":
            return (1.0, 1.0, 1.0, 1.0)
        elif cat == "Token.Keyword":
            return rgba_of_hex("#ff79c6");
        elif cat == "Token.Name":
            return rgba_of_hex("#f8f8f2")
        elif cat == "Token.Name.Builtin.Pseudo":
            return rgba_of_hex("#8be9fd")
        elif cat == "Token.Operator":
            return rgba_of_hex("#ff79c6")
        elif cat == "Token.Literal.Number.Integer":
            return rgba_of_hex("#bd93f9")
        else :
            return (1.0, 1.0, 1.0, 1.0)

    def post_frame(self, scene):
        # TODO update self.foreground_text
        frame = bpy.context.scene.frame_current
        for f,a in self.text_actions:
            if frame == f:
                a.act(self)

    def set_foreground_text(self, new_text):
        num_lines, num_cols = count_lines_and_columns(new_text)

        scale_cols = num_cols
        if num_cols < 20:
            scale_cols = 20

        padded_char_width = self.char_width * 1.04
        xscale = (self.foreground_width / 1.2) / (scale_cols * padded_char_width)
        yscale = (self.foreground_height / 1.2) / (num_lines * (self.line_height))
        scale = min(xscale, yscale)

        xpos = - padded_char_width * scale * num_cols / 2
        ypos = (self.line_height * scale * num_lines / 2) - 1.63 * self.char_height * scale

        self.foreground_text.location=(xpos,ypos,0.4)

        self.foreground_text.data.body = new_text
        self.foreground_text.scale = (scale, scale, scale)

    def pop_goal(self, goalId):
        for idx in range(len(self.goals)):
            if self.goals[idx].last_goalId() == goalId:
                return self.goals.pop(idx)

    def get_goal(self, goalId):
        for idx in range(len(self.goals)):
            if self.goals[idx].last_goalId() == goalId:
                return self.goals[idx]

    def add_goal(self, new_goal_json, appear_frame_count=20):
        goal = Goal(self, new_goal_json, appear_frame_count=appear_frame_count)
        self.current_frame = goal.last_frame()
        self.goals.append(goal)
        self.wait(self.wait_frame_count)

    def update_current_frame(self):
        for g in self.goals + self.dead_goals:
            gf = g.last_frame()
            if gf > self.current_frame:
                self.current_frame = gf

    def wait(self, frame_count, active_gids = dict()):
        self.current_frame += frame_count
        for g in self.goals:
            active = g.last_goalId() in active_gids
            g.insert_wait_action(self.current_frame, highlight=active)
        self.lay_out_goals()

    def update_scene_frame_end(self):
        if self.current_frame > bpy.context.scene.frame_end:
            bpy.context.scene.frame_end = self.current_frame

    def lay_out_goals(self):
        y = 0
        idx = len(self.goals) - 1
        while idx >= 0:
            g = self.goals[idx]
            g.set_last_location((0, -y, 0), self.current_frame)
            h = g.last_step().height
            y += h + 1.5
            idx = idx - 1

    def add_foreground_text_color_keyframe(self, color):
        self.foreground_text_material.diffuse_color = color
        self.foreground_text_material.keyframe_insert(data_path="diffuse_color", index=-1, frame=self.current_frame)

    def add_action(self, action_json):
        tactic_text = action_json["tacticText"]
        camera_start_goalsteps = []
        active_gids = set()
        for gaction in action_json["goalActions"]:
            gid = gaction["startGoalId"]
            active_gids.add(gid)
            goal = self.get_goal(gid)
            camera_start_goalsteps.append(goal.last_step())
        self.set_camera_keyframe(self.current_frame, camera_start_goalsteps)
        self.text_actions.append((self.current_frame, SetText(tactic_text)))
        self.add_foreground_text_color_keyframe(HIGHLIGHT_COLOR)

        self.wait(self.wait_frame_count, active_gids = active_gids)
        self.set_camera_keyframe(self.current_frame, camera_start_goalsteps)
        self.add_foreground_text_color_keyframe(HIGHLIGHT_COLOR)

        camera_end_goalsteps = []
        for gaction in action_json["goalActions"]:
            gid = gaction["startGoalId"]
            goal = self.pop_goal(gid)
            if goal is None:
                print("goal does not exist!", gid)
                continue

            rs = gaction['results']
            if len(rs) == 0:
                camera_end_goalsteps.append(goal.last_step())
                goal.add_done(frame_count = self.action_frame_count)
                self.dead_goals.append(goal)
            else:
                last_step = goal.last_step()
                # we want the first element in rs to end up as the final element
                # in self.goals.
                rs2 = rs.copy()
                rs2.reverse()
                for r in rs2[:-1]: # make any new Goal objects that are necessary
                    gr = Goal(self, last_step.goal_json,
                              appear_frame_count=1,
                              location = goal.last_step().location)

                    # todo: subtract one from usual frame_count, to account for the
                    # appear frame count above?
                    gr.add_action(last_step.state, r,
                                  continue_from_last = True,
                                  frame_count = self.action_frame_count)
                    camera_end_goalsteps.append(gr.last_step())
                    self.goals.append(gr)

                goal.add_action(gaction['startState'],
                                rs2[-1],
                                frame_count = self.action_frame_count)
                camera_end_goalsteps.append(goal.last_step())
                self.goals.append(goal)

        self.update_current_frame()
        self.text_actions.append((self.current_frame, ClearText()))
        self.add_foreground_text_color_keyframe(HIGHLIGHT_COLOR_TRANSPARENT)
        self.set_camera_keyframe(self.current_frame, camera_end_goalsteps)

        self.lay_out_goals()
        self.set_camera_keyframe(self.current_frame, camera_end_goalsteps)
        self.wait(self.post_tactic_pause_frame_count)
        self.set_camera_keyframe(self.current_frame, camera_end_goalsteps)

        if len(self.goals) == 0:
            self.text_actions.append((self.current_frame, GoalsAccomplished()))
            self.wait(self.wait_frame_count * 5)
        else:
            self.wait(self.switch_focus_frame_count)
        self.update_scene_frame_end()


    # goalIds is a list of goalIds
    def set_camera_keyframe(self, frame, goalsteps, zoom_out_factor = 1.3):
        #bpy.context.view_layer.update()
        assert(len(goalsteps) > 0)
        minx = math.inf
        miny = math.inf
        maxx = -math.inf
        maxy = -math.inf
        for gs in goalsteps:
            (lx, ly, _) = gs.location
            if lx < minx:
                minx = lx
            if ly > maxy:
                maxy = ly
            ux = lx + gs.width
            uy = ly - gs.height
            if ux > maxx:
                maxx = ux
            if uy < miny:
                miny = uy
        width = maxx - minx
        height = maxy - miny
        cx = minx + width / 2
        cy = miny + height / 2

        # account for occlusion from foreground panel.
        inner_resolution_y = (1 - self.foreground_ratio_y) * RESOLUTION_Y

        width2 = height / inner_resolution_y * RESOLUTION_X
        if width2 > width:
            # height of goals is the limiting factor
            width = width2
        else:
            # width of goals is the limiting factor
            # push the goals to the top of the visible area
            miny = maxy - width / RESOLUTION_X * inner_resolution_y
            height = maxy - miny
            cy = miny + height / 2

        full_height = height / (1 - self.foreground_ratio_y)
        zoomed_width = width * zoom_out_factor
        zoomed_height = height * zoom_out_factor
        zoomed_full_height = zoomed_height / (1 - self.foreground_ratio_y)
        cy = cy + (zoomed_full_height - zoomed_height) / 2
        CAMERA.location = (cx, cy, CAMERA_Z)
        CAMERA.keyframe_insert(data_path="location", index=-1, frame=frame)
        CAMERA.data.ortho_scale = width * zoom_out_factor
        CAMERA.data.keyframe_insert(data_path="ortho_scale", index=-1, frame=frame)

        panel_y_scale = zoomed_full_height/2 * self.foreground_ratio_y
        self.foreground.location = (cx,
                                    cy + full_height / 2 * zoom_out_factor - panel_y_scale,
                                    FOREGROUND_PANEL_Z)
        self.foreground.scale = (width * zoom_out_factor,
                                 width * zoom_out_factor,
                                 1)
        self.foreground.keyframe_insert(data_path="scale", index=-1, frame=frame)
        self.foreground.keyframe_insert(data_path="location", index=-1, frame=frame)


parser = argparse.ArgumentParser(prog="blender --python animate_proof.py --",
                                 description="animate a proof")
parser.add_argument("file", help="json file containing animation data")
parser.add_argument("--action_frame_count", type=int, default=40)
parser.add_argument("--wait_frame_count", type=int, default=15)
parser.add_argument("--post_tactic_pause_frame_count", type=int, default=2)
parser.add_argument("--switch_focus_frame_count", type=int, default=30)
parser.add_argument("--foreground_ratio_y", type=float, default=0.3)

script_args = []
found_double_dash = False
for arg in sys.argv:
    if found_double_dash:
        script_args.append(arg)
    if arg == "--":
        found_double_dash = True

args = parser.parse_args(script_args)

with open(args.file) as f:
    movie_json = json.load(f)

world = World(action_frame_count = args.action_frame_count,
              wait_frame_count = args.wait_frame_count,
              switch_focus_frame_count = args.switch_focus_frame_count,
              foreground_ratio_y = args.foreground_ratio_y,
              post_tactic_pause_frame_count = args.post_tactic_pause_frame_count)

world.init(movie_json)
