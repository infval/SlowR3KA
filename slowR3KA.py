#!/usr/bin/env python3
"""SlowR3KA - PSX Disassembler [PS1/Playstation 1]
"""


__version__ = "0.6.1"
__author__  = "infval"


import ast
import sys
from struct import unpack
from re import finditer
import tkinter as tk
from tkinter import ttk
from tkinter import font as tkfont
from tkinter import filedialog
from tkinter import messagebox


class PSXHeader:
    ATTR_NAMES = (
          "id", "text", "data", "pc0", "gp0"
        , "t_addr", "t_size"
        , "d_addr", "d_size"
        , "b_addr", "b_size"
        , "s_addr", "s_size"
        , "sp", "fp", "gp", "ret", "base"
        , "marker"
    )
    def __init__(self, data):
        marker_size = data.find(b"\x00", 76) - 76
        marker_size = max(0, min(0x800 - 76, marker_size))
        fmt = "<8s 17I {}s".format(marker_size)
        values = unpack(fmt, data[: 76 + marker_size])
        for key, value in zip(self.ATTR_NAMES, values):
            if type(value) == bytes:
                value = value.decode()
            setattr(self, key, value)

    def __str__(self):
        s = ("              #------------------#------------------#\n"
             "| Playstation | magic : {magic:} | pc0   : {pc:08X} |\n"
             "| Executable  | t_addr: {ta:08X} | t_size: {ts:08X} |\n"
             "| Information | s_addr: {sa:08X} | s_size: {ss:08X} |\n"
             "              #------------------#------------------#\n"
             "| {marker}"
            ).format(magic =self.id    , pc=self.pc0
                   , ta    =self.t_addr, ts=self.t_size
                   , sa    =self.s_addr, ss=self.s_size
                   , marker=self.marker)
        return s


REGS = (
      "zr", "at", "v0", "v1", "a0", "a1", "a2", "a3"
    , "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7"
    , "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7"
    , "t8", "t9", "k0", "k1", "gp", "sp", "fp", "ra"
)

def shift(data, shft, len_bit):
    return (data >> shft) & ((1 << len_bit) - 1)

def reg_shift(data, shft):
    return REGS[shift(data, shft, 5)]

ALLBITS = ( 0, 32)
OPCODE  = (26,  6)
SID     = ( 0,  6)
BID     = (16,  5)
CO      = (25,  1)
MVFUNC  = (21,  5)
TLBID   = ( 0, 25) # (0, 6)

START_ADDR = 0xF800

pc = 0x00000000
labels = []
bjal_set = set()

def int_to_s16(n):
    n &= 0xFFFF
    if n & 0x8000:
        n -= 0x10000
    return n
def offset_to_addr(base_addr, offset):
    return base_addr + (1 + int_to_s16(offset)) * 4

def Empty(inst, data):
    return inst
def Unknown(inst, data):
    return "{} 0x{:08X}".format(inst, data)
def COP(inst, data):
    return "{} 0x{:07X}".format(inst, shift(data, 0, 25))
def Bcond(inst, data):
    addr = offset_to_addr(pc, data)
    labels.append((pc, addr))
    if inst.upper() in ("BLTZAL", "BGEZAL"):
        bjal_set.add(addr)
    return "{} {}, 0x{:08X}".format(inst, reg_shift(data, 21), addr)
def JType(inst, data):
    addr = (shift(data, 0, 26) << 2) | (pc & 0xF0000000)
    labels.append((pc, addr))
    if inst.upper() == "JAL":
        bjal_set.add(addr)
    return "{} 0x{:08X}".format(inst, addr)
def BranchEqualFmt(inst, data):
    addr = offset_to_addr(pc, data)
    labels.append((pc, addr))
    return "{} {}, {}, 0x{:08X}".format(inst, reg_shift(data, 21),
        reg_shift(data, 16), addr)
def BranchZeroFmt(inst, data):
    addr = offset_to_addr(pc, data)
    labels.append((pc, addr))
    return "{} {}, 0x{:08X}".format(inst, reg_shift(data, 21), addr)
def ImmediateALU(inst, data):
    return "{} {}, {}, 0x{:04X}".format(inst, reg_shift(data, 16),
        reg_shift(data, 21), shift(data, 0, 16))
def ImmediateLUI(inst, data):
    return "{} {}, 0x{:04X}".format(inst, reg_shift(data, 16),
        shift(data, 0, 16))
def LoadStoreInstruction(inst, data):
    return "{} {}, 0x{:04X}({})".format(inst, reg_shift(data, 16),
        shift(data, 0, 16), reg_shift(data, 21))
def ShiftAmount(inst, data):
    return "{} {}, {}, 0x{:02X}".format(inst, reg_shift(data, 11),
        reg_shift(data, 16), shift(data, 6, 5))
def ShiftRegister(inst, data):
    return "{} {}, {}, {}".format(inst, reg_shift(data, 11),
        reg_shift(data, 16), reg_shift(data, 21))
def JumpTarget(inst, data):
    return "{} {}".format(inst, reg_shift(data, 21))
def JumpRegister(inst, data):
    return "{} {}, {}".format(inst, reg_shift(data, 11), reg_shift(data, 21))
def Special(inst, data):
    return "{} 0x{:05X}".format(inst, shift(data, 6, 20))
def MoveFromHILO(inst, data):
    return "{} {}".format(inst, reg_shift(data, 11))
def MoveToHILO(inst, data):
    return "{} {}".format(inst, reg_shift(data, 21))
def DivMult(inst, data):
    return "{} {}, {}".format(inst, reg_shift(data, 21), reg_shift(data, 16))
def RegisterALU(inst, data):
    return "{} {}, {}, {}".format(inst, reg_shift(data, 11),
        reg_shift(data, 21), reg_shift(data, 16))
def CoprocessorMove(inst, data):
    return "{} {}, {}".format(inst, reg_shift(data, 16), reg_shift(data, 11))
def BC(inst, data):
    return "{} 0x{:04X}".format(inst, shift(data, 0, 16))


itree = ("unknown", Unknown, OPCODE,
{
    0o00 : ("unknown", Unknown, SID, # SPECIAL
        {
            0o00 : ("sll", ShiftAmount, ALLBITS,
                {
                    0o00 : ("nop", Empty, (0,0),{})
                }
            )
          , 0o02 : ("srl"    , ShiftAmount,   (0,0),{})
          , 0o03 : ("sra"    , ShiftAmount,   (0,0),{})
          , 0o04 : ("sllv"   , ShiftRegister, (0,0),{})
          , 0o06 : ("srlv"   , ShiftRegister, (0,0),{})
          , 0o07 : ("srav"   , ShiftRegister, (0,0),{})
          , 0o10 : ("jr"     , JumpTarget,    (0,0),{})
          , 0o11 : ("jalr"   , JumpRegister,  (0,0),{})
          , 0o14 : ("syscall", Special,       (0,0),{})
          , 0o15 : ("break"  , Special,       (0,0),{})
          , 0o20 : ("mfhi"   , MoveFromHILO,  (0,0),{})
          , 0o21 : ("mthi"   , MoveToHILO,    (0,0),{})
          , 0o22 : ("mflo"   , MoveFromHILO,  (0,0),{})
          , 0o23 : ("mtlo"   , MoveToHILO,    (0,0),{})
          , 0o30 : ("mult"   , DivMult,       (0,0),{})
          , 0o31 : ("multu"  , DivMult,       (0,0),{})
          , 0o32 : ("div"    , DivMult,       (0,0),{})
          , 0o33 : ("divu"   , DivMult,       (0,0),{})
          , 0o40 : ("add"    , RegisterALU,   (0,0),{})
          , 0o41 : ("addu"   , RegisterALU,   (0,0),{})
          , 0o42 : ("sub"    , RegisterALU,   (0,0),{})
          , 0o43 : ("subu"   , RegisterALU,   (0,0),{})
          , 0o44 : ("and"    , RegisterALU,   (0,0),{})
          , 0o45 : ("or"     , RegisterALU,   (0,0),{})
          , 0o46 : ("xor"    , RegisterALU,   (0,0),{})
          , 0o47 : ("nor"    , RegisterALU,   (0,0),{})
          , 0o52 : ("slt"    , RegisterALU,   (0,0),{})
          , 0o53 : ("sltu"   , RegisterALU,   (0,0),{})
        }
    )
  , 0o01 : ("unknown", Unknown, BID, # BCOND (REGIMM)
        {
            0o00 : ("bltz"  , Bcond, (0,0),{})
          , 0o01 : ("bgez"  , Bcond, (0,0),{})
          , 0o20 : ("bltzal", Bcond, (0,0),{})
          , 0o21 : ("bgezal", Bcond, (0,0),{})
        }
    )
  , 0o02 : ("j"    , JType,          (0,0),{})
  , 0o03 : ("jal"  , JType,          (0,0),{})
  , 0o04 : ("beq"  , BranchEqualFmt, (0,0),{})
  , 0o05 : ("bne"  , BranchEqualFmt, (0,0),{})
  , 0o06 : ("blez" , BranchZeroFmt,  (0,0),{})
  , 0o07 : ("bgtz" , BranchZeroFmt,  (0,0),{})
  , 0o10 : ("addi" , ImmediateALU,   (0,0),{})
  , 0o11 : ("addiu", ImmediateALU,   (0,0),{})
  , 0o12 : ("slti" , ImmediateALU,   (0,0),{})
  , 0o13 : ("sltiu", ImmediateALU,   (0,0),{})
  , 0o14 : ("andi" , ImmediateALU,   (0,0),{})
  , 0o15 : ("ori"  , ImmediateALU,   (0,0),{})
  , 0o16 : ("xori" , ImmediateALU,   (0,0),{})
  , 0o17 : ("lui"  , ImmediateLUI,   (0,0),{})
  , 0o20 : ("unknown", Unknown, CO, # COP0
        {
            0o00 : ("unknown", Unknown, MVFUNC,
                {
                    0o00 : ("mfc0", CoprocessorMove, (0,0),{})
                  , 0o04 : ("mtc0", CoprocessorMove, (0,0),{})
                }
            )
          , 0o01 : ("cop0", COP, TLBID, # TLB
                {
                    0o01 : ("tlbr" , Empty, (0,0),{})
                  , 0o02 : ("tlbwi", Empty, (0,0),{})
                  , 0o06 : ("tlbwr", Empty, (0,0),{})
                  , 0o10 : ("tlbp" , Empty, (0,0),{})
                  , 0o20 : ("rfe"  , Empty, (0,0),{})
                }
            )
        }
    )
  , 0o21 : ("unknown", Unknown, CO, # COP1 (not valid for PSX)
        {
            0o00 : ("unknown", Unknown, MVFUNC,
                {
                    0o00 : ("mfc1", CoprocessorMove, (0,0),{})
                  , 0o02 : ("cfc1", CoprocessorMove, (0,0),{})
                  , 0o04 : ("mtc1", CoprocessorMove, (0,0),{})
                  , 0o06 : ("ctc1", CoprocessorMove, (0,0),{})
                  , 0o10 : ("unknown", Unknown, BID, # BC (cc = 0)
                        {
                            0o00 : ("bc1f", BC, (0,0),{})
                          , 0o01 : ("bc1t", BC, (0,0),{})
                        }
                    )
                }
            )
          , 0o01 : ("cop1", COP, (0,0),{})
        }
    )
  , 0o22 : ("unknown", Unknown, CO, # COP2 (GTE)
        {
            0o00 : ("unknown", Unknown, MVFUNC,
                {
                    0o00 : ("mfc2", CoprocessorMove, (0,0),{})
                  , 0o02 : ("cfc2", CoprocessorMove, (0,0),{})
                  , 0o04 : ("mtc2", CoprocessorMove, (0,0),{})
                  , 0o06 : ("ctc2", CoprocessorMove, (0,0),{})
                }
            )
          , 0o01 : ("cop2", COP, (0,0),{})
        }
    )
  , 0o23 : ("unknown", Unknown, CO, # COP3 (not valid for PSX)
        {
            0o00 : ("unknown", Unknown, MVFUNC,
                {
                    0o00 : ("mfc3", CoprocessorMove, (0,0),{})
                  , 0o02 : ("cfc3", CoprocessorMove, (0,0),{})
                  , 0o04 : ("mtc3", CoprocessorMove, (0,0),{})
                  , 0o06 : ("ctc3", CoprocessorMove, (0,0),{})
                }
            )
          , 0o01 : ("cop3", COP, (0,0),{})
        }
    )
  , 0o40 : ("lb"   , LoadStoreInstruction, (0,0),{})
  , 0o41 : ("lh"   , LoadStoreInstruction, (0,0),{})
  , 0o42 : ("lwl"  , LoadStoreInstruction, (0,0),{})
  , 0o43 : ("lw"   , LoadStoreInstruction, (0,0),{})
  , 0o44 : ("lbu"  , LoadStoreInstruction, (0,0),{})
  , 0o45 : ("lhu"  , LoadStoreInstruction, (0,0),{})
  , 0o46 : ("lwr"  , LoadStoreInstruction, (0,0),{})
  , 0o50 : ("sb"   , LoadStoreInstruction, (0,0),{})
  , 0o51 : ("sh"   , LoadStoreInstruction, (0,0),{})
  , 0o52 : ("swl"  , LoadStoreInstruction, (0,0),{})
  , 0o53 : ("sw"   , LoadStoreInstruction, (0,0),{})
  , 0o56 : ("swr"  , LoadStoreInstruction, (0,0),{})
  , 0o60 : ("lwc0" , LoadStoreInstruction, (0,0),{})
  , 0o61 : ("lwc1" , LoadStoreInstruction, (0,0),{}) # not valid for PSX
  , 0o62 : ("lwc2" , LoadStoreInstruction, (0,0),{})
  , 0o63 : ("lwc3" , LoadStoreInstruction, (0,0),{}) # not valid for PSX
  , 0o70 : ("swc0" , LoadStoreInstruction, (0,0),{})
  , 0o71 : ("swc1" , LoadStoreInstruction, (0,0),{}) # not valid for PSX
  , 0o72 : ("swc2" , LoadStoreInstruction, (0,0),{})
  , 0o73 : ("swc3" , LoadStoreInstruction, (0,0),{}) # not valid for PSX
})


def get_argparser():
    import argparse

    parser = argparse.ArgumentParser(description='SlowR3KA - PSX Disassembler [PS1/Playstation 1] v' + __version__)
    parser.add_argument('-v', '--version', action='version', version='%(prog)s ' + __version__)
    parser.add_argument('input_path', metavar='INPUT', help='PS-X EXE file or any file')
    parser.add_argument('output_path', metavar='OUTPUT', help='text file')
    parser.add_argument('-s', '--starting-address', metavar='RAM_ADDR', help='RAM address at the start of a file (default: 0x{:X})'.format(START_ADDR))
    fmt_group = parser.add_argument_group('format')
    fmt_group.add_argument('-n', '--no-labels', action='store_true', help='don\'t add labels')
    fmt_group.add_argument('--psig', action='store_true', help='PSIG compatible format')
    group = parser.add_mutually_exclusive_group()
    group.add_argument('-f' , nargs=2, metavar=('BEGIN', 'END') , help='file positions')
    group.add_argument('-fs', nargs=2, metavar=('BEGIN', 'SIZE'), help='file position and size of code')
    group.add_argument('-r' , nargs=2, metavar=('BEGIN', 'END') , help='RAM addresses')
    group.add_argument('-rs', nargs=2, metavar=('BEGIN', 'SIZE'), help='RAM address and size of code')

    return parser


class PSXDisassembler:
    def __init__(self, in_bytes=b""):
        self.header = None
        self.set_bytes(in_bytes)

        self.lines = []
        try: # Faster insertion
            from blist import blist
            self.lines = blist([])
        except ImportError:
            pass

    def set_bytes(self, in_bytes):
        self.in_bytes = in_bytes

        if self.in_bytes[:8] == b"PS-X EXE":
            self.header = PSXHeader(self.in_bytes)

            self.start = 0x800
            self.end = self.start + self.header.t_size
            self.size = self.header.t_size
            self.start_pc = self.header.t_addr - self.start
        else:
            self.start = 0
            self.end = len(self.in_bytes)
            self.size = self.end
            self.set_start_pc()

    def set_start_pc(self, sa=None):
        if sa is None:
            self.start_pc = START_ADDR
        else:
            self.start_pc = ast.literal_eval(sa)

    def set_start(self, start):
        self.start = ast.literal_eval(start)
        self.size = self.end - self.start
    def set_end(self, end):
        self.end = ast.literal_eval(end)
        self.size = self.end - self.start
    def set_start_ram(self, start):
        self.start = ast.literal_eval(start) - self.start_pc
        self.size = self.end - self.start
    def set_end_ram(self, end):
        self.end = ast.literal_eval(end) - self.start_pc
        self.size = self.end - self.start
    def set_size(self, size):
        self.size = ast.literal_eval(size)
        self.end = self.start + self.size

    def process(self, input_path, no_labels=False, psig=False):
        global pc, labels, bjal_set

        self.start = max(self.start, 0)
        self.end = min(self.end, len(self.in_bytes))
        self.end = self.start + (self.end - self.start) // 4 * 4

        pc = self.start_pc + self.start
        labels = []
        bjal_set = set()
        del self.lines[:]

        if psig:
            itree[3][0][3][0][3][0] = ("noop", Empty, (0,0),{}) # NOP -> NOOP
            line_format = lambda pc, func, inst, data: " {}\n".format(func(inst.upper(), data))
        else:
            itree[3][0][3][0][3][0] = ("nop", Empty, (0,0),{}) # Revert
            line_format = lambda pc, func, inst, data: "0x{:08X} {}\n".format(pc, func(inst.upper(), data))

        for word in range(self.start, self.end, 4):
            data, = unpack("<I", self.in_bytes[word: word+4])
            cur_node = itree
            while True:
                rule  = cur_node[2]
                nodes = cur_node[3]
                i = shift(data, *rule)
                if i in nodes:
                    cur_node = nodes[i]
                else:
                    inst = cur_node[0]
                    func = cur_node[1]
                    self.lines.append(line_format(pc, func, inst, data))
                    break
            pc += 4

        if not no_labels:
            new_labels = []
            for inst_addr, label_addr in labels:
                label_a_file = label_addr - self.start_pc
                if label_a_file >= self.start and label_a_file < self.end:
                    new_labels.append((inst_addr, label_addr))
            labels = new_labels

            if labels:
                prefixes = ("label", "func")

                for inst_addr, label_addr in labels:
                    p = prefixes[int(label_addr in bjal_set)]
                    label_name = "{}_0x{:08X}".format(p, label_addr)
                    inst_index = (inst_addr - self.start_pc - self.start) // 4
                    line = self.lines[inst_index].split(" ")
                    line[-1] = label_name + "\n"
                    self.lines[inst_index] = " ".join(line)

                labels.sort(key=lambda x: x[1], reverse=True)

                # Remove duplicates
                last = labels[-1]
                for i in range(len(labels)-2, -1, -1):
                    if last[1] == labels[i][1]:
                        del labels[i]
                    else:
                        last = labels[i]

                for inst_addr, label_addr in labels:
                    p = prefixes[int(label_addr in bjal_set)]
                    label_name = "{}_0x{:08X}".format(p, label_addr)
                    label_index = (label_addr - self.start_pc - self.start) // 4
                    self.lines.insert(label_index, label_name + ":\n")

        if psig:
            import os
            import datetime
            date = datetime.date.today().strftime("%d.%m.%Y")
            psig_header = [
                  ";{} {}\n".format(date, os.path.basename(input_path))
                , ";SlowR3KA v{}\n".format(__version__)
                , "\n"
                , " code_start {:X}\n".format(self.start + self.start_pc)
                , " file_index {:X}\n".format(self.start_pc)
                , "\n"
            ]
            if self.start_pc == START_ADDR or\
               self.start_pc == START_ADDR | 0x80000000:
                del psig_header[4]  # file_index
            self.lines = psig_header + self.lines

        return self.lines

    def write_to_file(self, output_path):
        with open(output_path, "w", encoding="utf-8") as f:
            f.writelines(self.lines)


class Application(tk.Frame):
    def __init__(self, master=None):
        super().__init__(master)

        self.pack(padx=8, pady=8, fill="both", expand=True)

        self.pd = PSXDisassembler()

        ttk.Style().configure("Error.TEntry", foreground="red")

        self.create_fonts()
        self.create_widgets()
        self.create_menu()

        self.master.bind("<KeyPress>", self.key_press)

        self.preview_pos = 0

        def mouse_wheel(e):
            self.preview_pos += (4 if e.delta < 0 else -4)
            self.update_preview(pos=self.preview_pos)
        self.code.bind("<MouseWheel>", mouse_wheel)

        self.show_info_id = None

    def show_info(self, text, clear=True):
        def clear_info():
            self.info_var.set("...")
            self.show_info_id = None

        if self.show_info_id is not None:
            self.after_cancel(self.show_info_id)
        self.info_var.set(text)
        if clear:
            self.show_info_id = self.after(3000, clear_info)

    def create_fonts(self):
        self.font_mono = tkfont.Font(family="Courier", size=10)
        fontname = ttk.Style().lookup("TLabel", "font")
        self.font_label_bold = tkfont.nametofont(fontname).copy()
        self.font_label_bold.configure(weight="bold")

    def create_widgets(self):
        frame_input_output = tk.Frame(self)
        frame_input_output.pack(fill="x")

        self.path_input_var  = tk.StringVar()
        self.path_output_var = tk.StringVar()

        for name, var, button_func in (
            ("Input", self.path_input_var, self.open_input)
          , ("Output", self.path_output_var, self.open_output)
        ):
            f = tk.Frame(frame_input_output)
            f.pack(fill="x")
            tmp = ttk.Label(f, text=name, width=8, anchor="w")
            tmp.pack(side="left")
            tmp = ttk.Entry(f, textvariable=var)
            tmp.pack(side="left", fill="x", expand=True)
            setattr(self, name.lower() + "_entry", tmp)
            tmp = ttk.Button(f, text="Browse", command=button_func)
            tmp.pack(side="left")

        frame_left_side = tk.Frame(self)
        frame_left_side.pack(anchor="nw", side="left", padx=2, pady=2)

        group_range = ttk.LabelFrame(frame_left_side, text="Range")
        group_range.pack(anchor="nw")

        # Starting address

        tmp = ttk.Label(group_range, text="Starting address",
                        font=self.font_label_bold)
        tmp.pack()

        def create_label_entry(master, text, var):
            f = tk.Frame(master)
            f.pack(anchor="w")
            tmp = ttk.Label(f, text=text, width=6)
            tmp.pack(side="left")
            entry = ttk.Entry(f, font=self.font_mono, width=11,
                              textvariable=var)
            entry.pack(side="left", padx=1, pady=1)
            return entry

        self.sa_var = tk.StringVar()
        sa_entry = create_label_entry(group_range, "", self.sa_var)

        # RAM addresses

        tmp = ttk.Label(group_range, text="RAM addresses",
                        font=self.font_label_bold)
        tmp.pack()

        self.rs_var = tk.StringVar()
        self.re_var = tk.StringVar()

        rs_entry = create_label_entry(group_range, "Start", self.rs_var)
        re_entry = create_label_entry(group_range, "End"  , self.re_var)

        # File positions

        tmp = ttk.Label(group_range, text="File positions",
                        font=self.font_label_bold)
        tmp.pack()

        self.fs_var = tk.StringVar()
        self.fe_var = tk.StringVar()
        self.sz_var = tk.StringVar()

        fs_entry = create_label_entry(group_range, "Start", self.fs_var)
        fe_entry = create_label_entry(group_range, "End"  , self.fe_var)

        tmp = ttk.Separator(group_range, orient="horizontal")
        tmp.pack(fill="x", pady=4)

        sz_entry = create_label_entry(group_range, "Size", self.sz_var)

        # Update Entry

        self.update_in_progress = False

        def gen_func(pd_func, var, entry):
            entry.configure(style="TEntry")
            if self.update_in_progress: return
            try:
                n = ast.literal_eval(var.get())
                if type(n) is not int:
                    raise ValueError
            except (SyntaxError, ValueError):
                entry.configure(style="Error.TEntry")
                return
            pd_func(var.get())
            self.update_in_progress = True
            self.update_all_vars(var)
            self.update_in_progress = False

        self.sa_var.trace("w", lambda *args:
            gen_func(self.pd.set_start_pc, self.sa_var, sa_entry))
        self.rs_var.trace("w", lambda *args:
            gen_func(self.pd.set_start_ram, self.rs_var, rs_entry))
        self.re_var.trace("w", lambda *args:
            gen_func(self.pd.set_end_ram, self.re_var, re_entry))
        self.fs_var.trace("w", lambda *args:
            gen_func(self.pd.set_start, self.fs_var, fs_entry))
        self.fe_var.trace("w", lambda *args:
            gen_func(self.pd.set_end, self.fe_var, fe_entry))
        self.sz_var.trace("w", lambda *args:
            gen_func(self.pd.set_size, self.sz_var, sz_entry))

        def load_file(*args):
            try:
                with open(self.path_input_var.get(), "rb") as f:
                    in_bytes = f.read()
            except (FileNotFoundError, PermissionError):
                self.show_info("Input File Error!")
                return
            self.pd.set_bytes(in_bytes)
            self.sa_var.set(hex(self.pd.start_pc))
            self.show_info("Input File Loaded")

        self.path_input_var.trace("w", load_file)

        # Format

        group_fmt = ttk.LabelFrame(frame_left_side, text="Format")
        group_fmt.pack(anchor="nw", fill="x")

        self.labels_var = tk.IntVar(value=1)
        self.psig_var   = tk.IntVar(value=0)
        tmp = ttk.Checkbutton(group_fmt, text="Labels",
                              variable=self.labels_var)
        tmp.pack(anchor="w")
        tmp = ttk.Checkbutton(group_fmt, text="PSIG compatible",
                              variable=self.psig_var)
        tmp.pack(anchor="w")

        # Process

        f = tk.Frame(self)
        f.pack(anchor="ne", fill="x")

        tmp = ttk.Button(f, text="Disassemble", command=self.process)
        tmp.pack(side="right")

        self.info_var = tk.StringVar(value="...")

        tmp = ttk.Label(f, textvariable=self.info_var,
                        font=self.font_label_bold)
        tmp.pack(side="left", padx=2)

        # Code preview

        self.code = tk.Text(self, wrap="none", width=34, font=self.font_mono)
        self.code.pack(anchor="nw", side="left", padx=2, pady=2,
                       fill="both", expand=True)

        self.code.config(cursor="arrow")
        self.code.config(state="disabled")

        self.sa_var.set(hex(self.pd.start_pc))

        # Code highlight
        self.code.config(bg="#272822", fg="#F8F8F2")
        self.code.tag_configure("ADDR"   , foreground="#808080")
        self.code.tag_configure("NUMBER" , foreground="#AE81FF")
        self.code.tag_configure("REG"    , foreground="#66D9EF")
        self.code.tag_configure("JUMP"   , foreground="#F92672")
        self.code.tag_configure("BRANCH" , foreground="#A6E22E")
        self.code.tag_configure("NOP"    , foreground="#FD971F")
        self.code.tag_configure("UNKNOWN", foreground="#75715E")

    def update_all_vars(self, exc=None):
        def set_var(var, value):
            v = var.get().upper()
            r = ""
            if v == "" or "X" in v: r = hex(value)
            elif "O" in v: r = oct(value)
            elif "B" in v: r = bin(value)
            else: r = str(value)
            var.set(r)
        if exc is not self.sa_var:
            set_var(self.sa_var, self.pd.start_pc)
        if exc is not self.rs_var:
            set_var(self.rs_var, self.pd.start + self.pd.start_pc)
        if exc is not self.re_var:
            set_var(self.re_var, self.pd.end + self.pd.start_pc)
        if exc is not self.fs_var:
            set_var(self.fs_var, self.pd.start)
        if exc is not self.fe_var:
            set_var(self.fe_var, self.pd.end)
        if exc is not self.sz_var:
            set_var(self.sz_var, self.pd.size)
        self.update_preview(exc is self.re_var or
                            exc is self.fe_var or
                            exc is self.sz_var)

    def update_preview(self, show_end=False, pos=None):
        text_font = tkfont.nametofont(self.code.cget("font"))
        linespace = text_font.metrics('linespace')
        code_height = int(self.code.winfo_height() / linespace)

        start = self.pd.start
        end = self.pd.end
        if show_end:
            self.pd.set_start(str(max(self.pd.end - code_height*4, start)))
        else:
            if pos is not None:
                self.pd.set_start(str(pos))
            self.pd.set_size(str(code_height * 4))

        self.preview_pos = self.pd.start

        result = self.pd.process("", True)
        if result:
            result[-1] = result[-1][:-1]  # Remove last \n

        self.code.config(state="normal")
        self.code.delete("1.0", "end")
        self.code.insert("end", "".join(result))
        self.code.config(state="disabled")

        # Code highlight
        for i in range(len(result)):
            self.code.tag_add("ADDR", "{}.0".format(i+1), "{}.10".format(i+1))
            si = result[i].find("0x", 1)
            if si > 0:
                ei = si + 2
                while ei < len(result[i]) and result[i][ei].isalnum():
                    ei += 1
                self.code.tag_add("NUMBER", "{}.{}".format(i+1, si),
                                  "{}.{}".format(i+1, ei))
            ei = result[i].find(" ", 11)
            if result[i][11] == "J":
                self.code.tag_add("JUMP", "{}.11".format(i+1),
                                  "{}.{}".format(i+1, ei))
            elif result[i][11] == "B" and result[i][11: 11 + 5] != "BREAK":
                self.code.tag_add("BRANCH", "{}.11".format(i+1),
                                  "{}.{}".format(i+1, ei))
            elif result[i][11: 11 + 3] == "NOP":
                self.code.tag_add("NOP", "{}.11".format(i+1),
                                  "{}.14".format(i+1))
            elif result[i][11: ei] == "UNKNOWN":
                self.code.tag_add("UNKNOWN", "{}.11".format(i+1),
                                  "{}.{}".format(i+1, ei))

            for reg in finditer(r"\W[a-z][a-z0-9]", result[i]):
                self.code.tag_add("REG", "{}.{}".format(i+1, reg.start()+1),
                                  "{}.{}".format(i+1, reg.end()))

        self.pd.set_start(str(start))
        self.pd.set_end(str(end))

    def create_menu(self):
        menubar = tk.Menu(self.master)

        filemenu = tk.Menu(menubar, tearoff=0)
        filemenu.add_command(label="Open", accelerator="Crtl+O",
                             command=self.open_input)
        filemenu.add_command(label="Save", accelerator="Crtl+S",
                             command=self.open_output)
        filemenu.add_separator()
        filemenu.add_command(label="Exit",
                             command=self.master.quit)
        menubar.add_cascade(label="File", menu=filemenu)

        actionmenu = tk.Menu(menubar, tearoff=0)
        actionmenu.add_command(label="Disassemble", accelerator="F5",
                               command=self.process)
        menubar.add_cascade(label="Action", menu=actionmenu)

        toolsmenu = tk.Menu(menubar, tearoff=0)
        toolsmenu.add_command(label="PS-X EXE header", accelerator="Crtl+H",
                              command=self.show_header)
        menubar.add_cascade(label="Tools", menu=toolsmenu)

        helpmenu = tk.Menu(menubar, tearoff=0)

        def cli():
            TextDialog(self, "CLI", get_argparser().format_help())
        helpmenu.add_command(label="Command-Line Interface", command=cli)
        helpmenu.add_command(label="About",
                             command=lambda: messagebox.showinfo("About", (
                                "PSX Disassembler\n"
                                "Program: SlowR3KA v{}\n"
                                "Author: {}".format(__version__, __author__))))
        menubar.add_cascade(label="Help", menu=helpmenu)

        self.master.config(menu=menubar)

    def key_press(self, e):
        if e.state == 0:
            if e.keycode == 116:  # F5
                self.process()
        elif e.state == 4:  # Ctrl+
            if e.keycode == ord("O"):
                self.open_input()
            elif e.keycode == ord("S"):
                self.open_output()
            elif e.keycode == ord("H"):
                self.show_header()

    def process(self):
        self.show_info("Wait...", False)
        self.update_idletasks()
        self.pd.process(self.path_input_var.get(),
                        not self.labels_var.get(), self.psig_var.get())
        try:
            self.pd.write_to_file(self.path_output_var.get())
        except (FileNotFoundError, PermissionError):
            self.show_info("Output File Error!")
            return
        self.show_info("Done!")

    def open_input(self):
        filetypes = [("All types", "*"),
                     ("PS-X EXE", "*.exe")]
        filename = filedialog.askopenfilename(filetypes=filetypes)
        if filename != "":
            self.path_input_var.set(filename)
            self.update_idletasks()
            self.input_entry.focus_set()
            self.input_entry.xview("end")
            self.input_entry.icursor("end")

    def open_output(self):
        filetypes = [("Text file", "*.txt"),
                     ("PSIG file", "*.psig"),
                     ("All types", "*")]
        if self.psig_var.get():
            filetypes[:2] = filetypes[1::-1]
        extension = filetypes[0][1].split(".")[-1]

        filename = filedialog.asksaveasfilename(filetypes=filetypes,
                                                defaultextension=extension)
        if filename != "":
            self.path_output_var.set(filename)
            self.update_idletasks()
            self.output_entry.focus_set()
            self.output_entry.xview("end")
            self.output_entry.icursor("end")

    def show_header(self):
        TextDialog(self, "PS-X EXE header", str(self.pd.header))


class TextDialog(tk.Toplevel):
    def __init__(self, master=None, title="", text=""):
        super().__init__(master)

        self.title(title)

        self.t = tk.Text(self)
        self.t.pack(fill="both", expand=True, padx=8, pady=8)

        self.t.config(cursor="arrow")
        self.t.insert("end", text)
        self.t.config(state="disabled")

        self.bind("<Escape>", lambda e: self.destroy())


def main_gui():
    root = tk.Tk()

    icon_png_base64 = "\
iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAMAAAAoLQ9TAAAAD1BMVEX////AAPCA\
ALAAQPAAAACJZj94AAAARUlEQVR4AXWNAQoAIAwCXfP/b66VGBUp2DyEkFPhQHIo\
EIoF3AXcBXb/LQ7y+WUUhYGVABoryqx3HkSzsTq9fBea2XmpA17fAl1K6MtCAAAA\
AElFTkSuQmCC"

    img = tk.PhotoImage(data=icon_png_base64)
    root.tk.call('wm', 'iconphoto', root._w, '-default', img)
    root.title("SlowR3KA v" + __version__)

    app = Application(master=root)
    app.mainloop()


def main_cli():
    parser = get_argparser()
    args = parser.parse_args()

    try:
        with open(args.input_path, "rb") as f:
            in_bytes = f.read()
    except (FileNotFoundError, PermissionError) as err:
        print("File Error: {}".format(err))
        sys.exit(1)

    pd = PSXDisassembler(in_bytes)
    if args.starting_address:
        pd.set_start_pc(args.starting_address)

    funs = [(pd.set_start, pd.set_end),
            (pd.set_start, pd.set_size),
            (pd.set_start_ram, pd.set_end_ram),
            (pd.set_start_ram, pd.set_size)]
    for i, v in enumerate([args.f, args.fs, args.r, args.rs]):
        if v:
            funs[i][0](v[0])
            funs[i][1](v[1])
            break

    if pd.header is not None:
        print(pd.header)

    pd.process(args.input_path, args.no_labels, args.psig)
    pd.write_to_file(args.output_path)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        main_gui()
    else:
        main_cli()
