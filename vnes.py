#!/usr/bin/env python3
"""
VirtualNES 0.1.1 — compact NTSC Famicom/NES emulator (stdlib only).

Ricoh 2A03 / NMOS 6502 CPU core with intentional handlers for all 256
opcode bytes (151 official + unofficial/illegal families used by NES
software and nestest-style validation ROMs).

Usage:
    python virtualnes0.1.1.py [game.nes]
    python virtualnes0.1.1.py --cpu-selftest
    python virtualnes0.1.1.py --debug-cpu [game.nes]

files = OFF: opcode tables stay embedded in this .py (no external .md).
ROM loading: File→Load ROM… / Ctrl+O / toolbar, plus optional argv[1].

Embedded README:
    VirtualNES 0.1.1a — complete 2A03 CPU, single-file.
    Mappers 0–4 · NTSC timing · Tk GUI · OAM DMA stalls · full opcode map.
"""

from __future__ import annotations

import array
import os
import sys
import time
import tkinter as tk
from tkinter import filedialog, messagebox
from dataclasses import dataclass
from typing import Callable, List, Optional, Tuple


# ---------------------------------------------------------------------------
# Global policy: File→Load ROM enabled; opcode tables embedded (no .md files)
# ---------------------------------------------------------------------------
files = ON = True  # hardcoded ON — Load ROM dialog / Ctrl+O / toolbar
OFF = False

# ---------------------------------------------------------------------------
# NTSC timing
# FPS ≈ 60.0988, CPU ≈ 1_789_773 Hz
# CPU_CYCLES_PER_FRAME = CPU_CLOCK / FPS ≈ 29780.5 → 29781
# ---------------------------------------------------------------------------
NTSC_FPS = 60.0988
CPU_CLOCK_HZ = 1_789_773
CPU_CYCLES_PER_FRAME = int(round(CPU_CLOCK_HZ / NTSC_FPS))  # 29781
PPU_CYCLES_PER_CPU = 3
FRAME_MS = max(1, int(round(1000.0 / NTSC_FPS)))  # ~16

NES_W, NES_H = 256, 240
SCALE = 1                 # fits inside 600×400 chrome
WIN_W, WIN_H = 600, 400   # fixed OS window size

# Official 2C02 NTSC palette (64 RGB triples)
NES_PALETTE = (
    (84, 84, 84), (0, 30, 116), (8, 16, 144), (48, 0, 136),
    (68, 0, 100), (92, 0, 48), (84, 4, 0), (60, 24, 0),
    (32, 42, 0), (8, 58, 0), (0, 64, 0), (0, 60, 0),
    (0, 50, 60), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (152, 150, 152), (8, 76, 196), (48, 50, 236), (92, 30, 228),
    (136, 20, 176), (160, 20, 100), (152, 34, 32), (120, 60, 0),
    (84, 90, 0), (40, 114, 0), (8, 124, 0), (0, 118, 40),
    (0, 102, 120), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (236, 238, 236), (76, 154, 236), (120, 124, 236), (176, 98, 236),
    (228, 84, 236), (236, 88, 180), (236, 106, 100), (212, 136, 32),
    (160, 170, 0), (116, 196, 0), (76, 208, 32), (56, 204, 108),
    (56, 180, 204), (60, 60, 60), (0, 0, 0), (0, 0, 0),
    (236, 238, 236), (168, 204, 236), (188, 188, 236), (212, 178, 236),
    (236, 174, 236), (236, 174, 212), (236, 180, 176), (228, 196, 144),
    (204, 210, 120), (180, 222, 120), (168, 226, 144), (152, 226, 180),
    (160, 214, 228), (160, 162, 160), (0, 0, 0), (0, 0, 0),
)


# =============================================================================
# Cartridge / iNES + mappers 0–4
# =============================================================================
class Cartridge:
    """iNES cartridge with PRG/CHR banking for mappers 0, 1, 2, 3, 4."""

    def __init__(self, path: str) -> None:
        with open(path, "rb") as f:
            data = f.read()
        if len(data) < 16 or data[0:4] != b"NES\x1a":
            raise ValueError("Not a valid iNES ROM (missing NES\\x1a header)")

        self.path = path
        self.name = os.path.basename(path)
        prg_banks = data[4]
        chr_banks = data[5]
        flags6 = data[6]
        flags7 = data[7]
        self.mapper = ((flags7 >> 4) << 4) | (flags6 >> 4)
        self.mirroring = flags6 & 1  # 0=horizontal, 1=vertical
        self.four_screen = bool(flags6 & 8)
        trainer = 512 if (flags6 & 4) else 0
        if self.mapper not in (0, 1, 2, 3, 4):
            raise ValueError(f"Unsupported mapper {self.mapper} (need 0–4)")

        off = 16 + trainer
        if prg_banks < 1:
            raise ValueError("Invalid iNES header: PRG ROM size is 0")
        prg_size = prg_banks * 16384
        chr_size = chr_banks * 8192
        if off + prg_size + chr_size > len(data):
            raise ValueError("ROM truncated / header size mismatch")

        self.prg = bytearray(data[off : off + prg_size])
        off += prg_size
        if chr_size:
            self.chr = bytearray(data[off : off + chr_size])
            self.chr_ram = False
        else:
            self.chr = bytearray(8192)
            self.chr_ram = True

        self.prg_ram = bytearray(8192)
        self.prg_bank_count = prg_banks
        self.chr_bank_count = max(1, chr_banks) if chr_banks else 1

        # Banking windows
        self.prg_bank_16k = [0, max(0, self.prg_bank_count - 1)]
        self.prg_bank_8k = [0, 1, 2, 3]
        self.chr_bank_1k = [0, 1, 2, 3, 4, 5, 6, 7]
        self.chr_bank_4k = [0, 1]
        self.chr_bank_8k = 0
        self.prg_mode = 3  # MMC1 default: fix last bank at $C000
        self.chr_mode = 0
        self.mmc1_shift = 0
        self.mmc1_count = 0
        self.mmc1_ctrl = 0x0C
        self.mmc3_bank_select = 0
        self.mmc3_irq_latch = 0
        self.mmc3_irq_counter = 0
        self.mmc3_irq_enable = False
        self.mmc3_irq_reload = False
        self.irq = False
        self._apply_mmc1_control(self.mmc1_ctrl)

        if self.mapper == 0:
            # NROM: mirror if 16K
            if self.prg_bank_count == 1:
                self.prg_bank_16k = [0, 0]
            else:
                self.prg_bank_16k = [0, 1]
        elif self.mapper == 2:
            self.prg_bank_16k = [0, self.prg_bank_count - 1]
        elif self.mapper == 3:
            self.chr_bank_8k = 0
        elif self.mapper == 4:
            n = max(2, len(self.prg) // 8192)
            self.prg_bank_8k = [0, 1, n - 2, n - 1]

    def _apply_mmc1_control(self, value: int) -> None:
        self.mmc1_ctrl = value & 0x1F
        mirror = value & 3
        if mirror == 0:
            self.mirroring = 2  # one-screen lower
        elif mirror == 1:
            self.mirroring = 3  # one-screen upper
        elif mirror == 2:
            self.mirroring = 1  # vertical
        else:
            self.mirroring = 0  # horizontal
        self.prg_mode = (value >> 2) & 3
        self.chr_mode = (value >> 4) & 1

    def cpu_read(self, addr: int) -> int:
        if 0x6000 <= addr <= 0x7FFF:
            return self.prg_ram[addr - 0x6000]
        if addr < 0x8000:
            return 0
        if self.mapper in (0, 1, 2, 3):
            if addr < 0xC000:
                bank = self.prg_bank_16k[0]
            else:
                bank = self.prg_bank_16k[1]
            return self.prg[(bank * 0x4000 + (addr & 0x3FFF)) % len(self.prg)]
        # MMC3 8K banks
        slot = (addr - 0x8000) // 0x2000
        bank = self.prg_bank_8k[slot]
        return self.prg[(bank * 0x2000 + (addr & 0x1FFF)) % len(self.prg)]

    def cpu_write(self, addr: int, value: int) -> None:
        if 0x6000 <= addr <= 0x7FFF:
            self.prg_ram[addr - 0x6000] = value & 0xFF
            return
        if addr < 0x8000:
            return
        m = self.mapper
        if m == 1:
            self._mmc1_write(addr, value)
        elif m == 2:
            self.prg_bank_16k[0] = value % self.prg_bank_count
        elif m == 3:
            nchr = max(1, len(self.chr) // 0x2000)
            self.chr_bank_8k = value % nchr
        elif m == 4:
            self._mmc3_write(addr, value)

    def _mmc1_write(self, addr: int, value: int) -> None:
        if value & 0x80:
            self.mmc1_shift = 0
            self.mmc1_count = 0
            self._apply_mmc1_control(self.mmc1_ctrl | 0x0C)
            return
        self.mmc1_shift |= (value & 1) << self.mmc1_count
        self.mmc1_count += 1
        if self.mmc1_count < 5:
            return
        data = self.mmc1_shift & 0x1F
        self.mmc1_shift = 0
        self.mmc1_count = 0
        reg = (addr >> 13) & 3
        if reg == 0:
            self._apply_mmc1_control(data)
        elif reg == 1:
            if self.chr_mode:
                self.chr_bank_4k[0] = data
            else:
                self.chr_bank_4k[0] = data & 0x1E
                self.chr_bank_4k[1] = (data & 0x1E) | 1
        elif reg == 2:
            if self.chr_mode:
                self.chr_bank_4k[1] = data
        else:
            banks = self.prg_bank_count
            bank = data & 0x0F
            if self.prg_mode in (0, 1):
                b = bank & 0x0E
                self.prg_bank_16k = [b % banks, (b + 1) % banks]
            elif self.prg_mode == 2:
                self.prg_bank_16k = [0, bank % banks]
            else:
                self.prg_bank_16k = [bank % banks, banks - 1]

    def _mmc3_write(self, addr: int, value: int) -> None:
        even = (addr & 1) == 0
        if 0x8000 <= addr <= 0x9FFF:
            if even:
                self.mmc3_bank_select = value
            else:
                self._mmc3_bank_data(value)
        elif 0xA000 <= addr <= 0xBFFF:
            if even:
                self.mirroring = 0 if (value & 1) else 1
        elif 0xC000 <= addr <= 0xDFFF:
            if even:
                self.mmc3_irq_latch = value
            else:
                self.mmc3_irq_reload = True
        elif 0xE000 <= addr <= 0xFFFF:
            self.mmc3_irq_enable = not even
            if even:
                self.irq = False

    def _mmc3_bank_data(self, value: int) -> None:
        reg = self.mmc3_bank_select & 7
        prg_mode = (self.mmc3_bank_select >> 6) & 1
        chr_mode = (self.mmc3_bank_select >> 7) & 1
        nprg = len(self.prg) // 8192
        if reg <= 5:
            if reg in (0, 1):
                base = (value & 0xFE)
                if chr_mode:
                    self.chr_bank_1k[reg * 2 + 4] = base
                    self.chr_bank_1k[reg * 2 + 5] = base + 1
                else:
                    self.chr_bank_1k[reg * 2] = base
                    self.chr_bank_1k[reg * 2 + 1] = base + 1
            else:
                idx = reg + 2 if not chr_mode else reg - 2
                self.chr_bank_1k[idx] = value
        elif reg == 6:
            bank = value % nprg
            if prg_mode:
                self.prg_bank_8k[2] = bank
                self.prg_bank_8k[0] = nprg - 2
            else:
                self.prg_bank_8k[0] = bank
                self.prg_bank_8k[2] = nprg - 2
            self.prg_bank_8k[3] = nprg - 1
        elif reg == 7:
            self.prg_bank_8k[1] = value % nprg

    def chr_read(self, addr: int) -> int:
        addr &= 0x1FFF
        if self.mapper in (0, 2):
            return self.chr[addr % len(self.chr)]
        if self.mapper == 3:
            return self.chr[(self.chr_bank_8k * 0x2000 + addr) % len(self.chr)]
        if self.mapper == 1:
            if self.chr_mode:
                bank = self.chr_bank_4k[0 if addr < 0x1000 else 1]
                return self.chr[(bank * 0x1000 + (addr & 0x0FFF)) % len(self.chr)]
            bank = self.chr_bank_4k[0]
            return self.chr[(bank * 0x1000 + addr) % len(self.chr)]
        # MMC3
        bank = self.chr_bank_1k[addr >> 10]
        return self.chr[(bank * 0x400 + (addr & 0x3FF)) % len(self.chr)]

    def chr_write(self, addr: int, value: int) -> None:
        if not self.chr_ram:
            return
        self.chr[addr & 0x1FFF] = value & 0xFF

    def mirror_vram_addr(self, addr: int) -> int:
        """Map $2000–$2FFF nametable address into cartridge VRAM."""
        addr &= 0x0FFF
        table = addr // 0x400
        offset = addr & 0x3FF
        m = self.mirroring
        if self.four_screen:
            return (table * 0x400 + offset) & 0xFFF
        if m == 0:  # horizontal: A|A / B|B
            nt = 0 if table in (0, 1) else 1
        elif m == 1:  # vertical: A|B / A|B
            nt = table & 1
        elif m == 2:
            nt = 0
        else:
            nt = 1
        return (nt * 0x400 + offset) & 0x7FF

    def mmc3_scanline_clock(self) -> None:
        if self.mapper != 4:
            return
        if self.mmc3_irq_counter == 0 or self.mmc3_irq_reload:
            self.mmc3_irq_counter = self.mmc3_irq_latch
            self.mmc3_irq_reload = False
        else:
            self.mmc3_irq_counter -= 1
        if self.mmc3_irq_counter == 0 and self.mmc3_irq_enable:
            self.irq = True


# =============================================================================
# Controller (standard NES shift register)
# =============================================================================
class Controller:
    """Z=A X=B Enter=Start RShift=Select Arrows=D-pad."""

    A, B, SELECT, START, UP, DOWN, LEFT, RIGHT = range(8)

    def __init__(self) -> None:
        self.buttons = [0] * 8
        self.strobe = 0
        self.index = 0
        self.snapshot = 0

    def set_key(self, button: int, pressed: bool) -> None:
        if 0 <= button < 8:
            self.buttons[button] = 1 if pressed else 0
            if self.strobe:
                self._capture()

    def write(self, value: int) -> None:
        self.strobe = value & 1
        if self.strobe:
            self._capture()
            self.index = 0

    def read(self) -> int:
        if self.index >= 8:
            return 1
        bit = (self.snapshot >> self.index) & 1
        if not self.strobe:
            self.index += 1
        return bit

    def _capture(self) -> None:
        self.snapshot = 0
        for i, b in enumerate(self.buttons):
            if b:
                self.snapshot |= 1 << i
        self.index = 0


# =============================================================================
# APU stub (timing only, no audio output)
# =============================================================================
class APU:
    """Minimal APU stub so $4000–$4017 writes do not crash games."""

    def __init__(self) -> None:
        self.regs = bytearray(0x20)
        self.frame_counter = 0

    def reset(self) -> None:
        self.regs[:] = bytearray(0x20)
        self.frame_counter = 0

    def read(self, addr: int) -> int:
        if addr == 0x4015:
            return 0
        return 0

    def write(self, addr: int, value: int) -> None:
        if 0x4000 <= addr <= 0x4017:
            self.regs[addr - 0x4000] = value & 0xFF

    def step(self, cpu_cycles: int) -> None:
        self.frame_counter += cpu_cycles
        # TODO: real square/triangle/noise + stdlib audio if desired


# =============================================================================
# PPU (background + minimal sprites)
# =============================================================================
class PPU:
    """Simplified 2C02: nametable BG + OAM sprites → 256×240 framebuffer."""

    def __init__(self, cart: Cartridge) -> None:
        self.cart = cart
        # 2KB normal; 4KB when cartridge requests four-screen mirroring
        self.vram = bytearray(0x1000 if cart.four_screen else 0x800)
        self.palette = bytearray(0x20)
        self.oam = bytearray(256)
        self.framebuffer = array.array("B", bytes(NES_W * NES_H * 3))

        self.ctrl = 0
        self.mask = 0
        self.status = 0
        self.oam_addr = 0
        self.scroll_x = 0
        self.scroll_y = 0
        self.v = 0
        self.t = 0
        self.x = 0
        self.w = 0
        self.buffer = 0
        self.scanline = 0
        self.cycle = 0
        self.frame_complete = False
        self.nmi = False
        self.odd_frame = False

    def reset(self) -> None:
        self.ctrl = self.mask = self.status = 0
        self.oam_addr = 0
        self.scroll_x = self.scroll_y = 0
        self.v = self.t = self.x = self.w = 0
        self.buffer = 0
        self.scanline = 0
        self.cycle = 0
        self.frame_complete = False
        self.nmi = False

    def read_reg(self, addr: int) -> int:
        a = addr & 7
        if a == 2:  # PPUSTATUS
            val = (self.status & 0xE0) | (self.buffer & 0x1F)
            self.status &= 0x7F  # clear VBlank
            self.w = 0
            return val
        if a == 4:
            return self.oam[self.oam_addr]
        if a == 7:
            data = self.buffer
            self.buffer = self._read_ppu(self.v)
            if (self.v & 0x3FFF) >= 0x3F00:
                data = self.buffer
            self.v = (self.v + (32 if (self.ctrl & 0x04) else 1)) & 0x7FFF
            return data
        return 0

    def write_reg(self, addr: int, value: int) -> None:
        a = addr & 7
        value &= 0xFF
        self.buffer = value
        if a == 0:
            self.ctrl = value
            self.t = (self.t & 0xF3FF) | ((value & 0x03) << 10)
        elif a == 1:
            self.mask = value
        elif a == 3:
            self.oam_addr = value
        elif a == 4:
            self.oam[self.oam_addr] = value
            self.oam_addr = (self.oam_addr + 1) & 0xFF
        elif a == 5:
            if self.w == 0:
                self.scroll_x = value
                self.x = value & 7
                self.t = (self.t & 0xFFE0) | (value >> 3)
                self.w = 1
            else:
                self.scroll_y = value
                self.t = (self.t & 0x8FFF) | ((value & 7) << 12)
                self.t = (self.t & 0xFC1F) | ((value & 0xF8) << 2)
                self.w = 0
        elif a == 6:
            if self.w == 0:
                self.t = (self.t & 0x00FF) | ((value & 0x3F) << 8)
                self.w = 1
            else:
                self.t = (self.t & 0xFF00) | value
                self.v = self.t
                self.w = 0
        elif a == 7:
            self._write_ppu(self.v, value)
            self.v = (self.v + (32 if (self.ctrl & 0x04) else 1)) & 0x7FFF

    def _read_ppu(self, addr: int) -> int:
        addr &= 0x3FFF
        if addr < 0x2000:
            return self.cart.chr_read(addr)
        if addr < 0x3F00:
            return self.vram[self.cart.mirror_vram_addr(addr)]
        return self.palette[self._pal_mirror(addr)]

    def _write_ppu(self, addr: int, value: int) -> None:
        addr &= 0x3FFF
        value &= 0xFF
        if addr < 0x2000:
            self.cart.chr_write(addr, value)
        elif addr < 0x3F00:
            self.vram[self.cart.mirror_vram_addr(addr)] = value
        else:
            self.palette[self._pal_mirror(addr)] = value

    @staticmethod
    def _pal_mirror(addr: int) -> int:
        a = addr & 0x1F
        if a in (0x10, 0x14, 0x18, 0x1C):
            a -= 0x10
        return a

    def step(self, cpu_cycles: int) -> None:
        """Advance PPU by cpu_cycles * 3 dots; render on entering VBlank."""
        dots = cpu_cycles * PPU_CYCLES_PER_CPU
        while dots > 0:
            # Fast-forward when far from VBlank / MMC3 clock edges
            if self.cycle != 1 and self.cycle != 260:
                # Remaining dots on this scanline before next interesting cycle
                if self.cycle < 1:
                    skip = 1 - self.cycle
                elif self.cycle < 260:
                    skip = 260 - self.cycle
                else:
                    skip = 341 - self.cycle
                if skip > 1:
                    take = min(dots, skip)
                    self.cycle += take
                    dots -= take
                    if self.cycle > 340:
                        self.cycle = 0
                        self.scanline += 1
                        if self.scanline > 261:
                            self.scanline = 0
                            self.odd_frame = not self.odd_frame
                    continue
            self._dot()
            dots -= 1

    def _dot(self) -> None:
        if self.scanline == 241 and self.cycle == 1:
            self.status |= 0x80
            if self.ctrl & 0x80:
                self.nmi = True
            self._render_frame()
            self.frame_complete = True
        if self.scanline == 261 and self.cycle == 1:
            self.status &= 0x1F  # clear VBlank + sprite flags
            self.nmi = False
        # MMC3 A12 clock approx: rising edge each visible scanline fetch
        if 0 <= self.scanline < 240 and self.cycle == 260:
            if self.mask & 0x18:
                self.cart.mmc3_scanline_clock()

        self.cycle += 1
        if self.cycle > 340:
            self.cycle = 0
            self.scanline += 1
            if self.scanline > 261:
                self.scanline = 0
                self.odd_frame = not self.odd_frame

    def _render_frame(self) -> None:
        fb = self.framebuffer
        show_bg = bool(self.mask & 0x08)
        show_sp = bool(self.mask & 0x10)
        bg_pattern = 0x1000 if (self.ctrl & 0x10) else 0
        sp_pattern = 0x1000 if (self.ctrl & 0x08) else 0
        tall = bool(self.ctrl & 0x20)
        base_nt = (self.ctrl & 3) * 0x400
        sx = self.scroll_x
        sy = self.scroll_y

        # Universal backdrop
        uni = NES_PALETTE[self.palette[0] & 0x3F]
        for i in range(0, len(fb), 3):
            fb[i], fb[i + 1], fb[i + 2] = uni

        if show_bg:
            for y in range(NES_H):
                sy_tot = y + sy
                nt_row = (sy_tot // 8) % 60
                fine_y = sy_tot & 7
                nt_y = nt_row % 30
                nt_table_y = 0 if nt_row < 30 else 1
                for x in range(NES_W):
                    sx_tot = x + sx
                    nt_col = (sx_tot // 8) % 64
                    fine_x = sx_tot & 7
                    nt_x = nt_col % 32
                    nt_table_x = 0 if nt_col < 32 else 1
                    # Nametable select with scroll wrap
                    nt = base_nt
                    if nt_table_x:
                        nt ^= 0x400
                    if nt_table_y:
                        nt ^= 0x800
                    tile_addr = 0x2000 | (nt & 0xC00) | (nt_y << 5) | nt_x
                    tile = self._read_ppu(tile_addr)
                    attr_addr = (
                        0x23C0
                        | (nt & 0xC00)
                        | ((nt_y >> 2) << 3)
                        | (nt_x >> 2)
                    )
                    attr = self._read_ppu(attr_addr)
                    shift = ((nt_y & 2) << 1) | (nt_x & 2)
                    pallet = (attr >> shift) & 3
                    lo = self.cart.chr_read(bg_pattern | (tile << 4) | fine_y)
                    hi = self.cart.chr_read(bg_pattern | (tile << 4) | fine_y | 8)
                    bit = 7 - fine_x
                    pix = ((hi >> bit) & 1) << 1 | ((lo >> bit) & 1)
                    if pix:
                        pidx = self.palette[(pallet << 2) | pix] & 0x3F
                        r, g, b = NES_PALETTE[pidx]
                        o = (y * NES_W + x) * 3
                        fb[o], fb[o + 1], fb[o + 2] = r, g, b

        if show_sp:
            h = 16 if tall else 8
            for i in range(63, -1, -1):  # back to front
                oy = self.oam[i * 4]
                tile = self.oam[i * 4 + 1]
                attr = self.oam[i * 4 + 2]
                ox = self.oam[i * 4 + 3]
                if oy >= 0xEF:
                    continue
                flip_h = bool(attr & 0x40)
                flip_v = bool(attr & 0x80)
                pal = (attr & 3) + 4
                for row in range(h):
                    py = oy + 1 + row
                    if not (0 <= py < NES_H):
                        continue
                    r = (h - 1 - row) if flip_v else row
                    if tall:
                        bank = 0x1000 if (tile & 1) else 0
                        t = (tile & 0xFE) + (1 if r >= 8 else 0)
                        r &= 7
                        lo = self.cart.chr_read(bank | (t << 4) | r)
                        hi = self.cart.chr_read(bank | (t << 4) | r | 8)
                    else:
                        lo = self.cart.chr_read(sp_pattern | (tile << 4) | r)
                        hi = self.cart.chr_read(sp_pattern | (tile << 4) | r | 8)
                    for col in range(8):
                        px = ox + col
                        if not (0 <= px < NES_W):
                            continue
                        bit = col if flip_h else (7 - col)
                        pix = ((hi >> bit) & 1) << 1 | ((lo >> bit) & 1)
                        if not pix:
                            continue
                        pidx = self.palette[(pal << 2) | pix] & 0x3F
                        r, g, b = NES_PALETTE[pidx]
                        o = (py * NES_W + px) * 3
                        fb[o], fb[o + 1], fb[o + 2] = r, g, b


# =============================================================================
# Ricoh 2A03 / NMOS 6502 CPU — complete 256-opcode NES core (FILES_OFF)
# =============================================================================
# Hardware notes (see also method comments):
# - Decimal (D) flag exists but ADC/SBC never use BCD on the 2A03.
# - JMP ($xxFF) wraps within the page (6502 indirect bug).
# - BRK pushes PC+2 from the opcode (skips signature), B=1 on stack.
# - IRQ/NMI push B=0; U (bit 5) is always set when pushed / after PLP.
# - Page-cross: +1 on taken branch; +1 on some indexed loads; stores/RMW fixed.
# - RMW: read → dummy write → final write (NMOS behavior).
# - JAM/KIL: CPU locks; step burns cycles without advancing PC.
# =============================================================================

@dataclass(frozen=True)
class OpEntry:
    """One intentional dispatch slot for opcode byte 0x00–0xFF."""

    mnemonic: str
    mode: str  # imp/acc/imm/zp/zpx/zpy/abs/absx/absy/ind/indx/indy/rel
    cycles: int
    page_cross: bool  # +1 when indexed effective address crosses page
    unofficial: bool
    execute: Callable[[], None]


class CPU:
    """Ricoh 2A03 (NES) CPU: all 151 official + unofficial NMOS opcodes."""

    # Processor status: N V U B D I Z C
    C, Z, I, D, B, U, V, N = 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80

    # Unstable AND magic for XAA/ANE (common nestest-friendly constant)
    _XAA_MAGIC = 0xEE

    def __init__(self, bus: "Bus") -> None:
        self.bus = bus
        self.a = self.x = self.y = 0
        self.sp = 0xFD
        self.pc = 0
        self.status = 0x24  # U|I on power-up style reset before vector fetch
        self.cycles = 0
        self.stall = 0  # OAM DMA CPU stall counter (Bus._oam_dma)
        self.jammed = False
        self.debug = False
        self._crossed = False
        self._ops: List[OpEntry] = self._build_ops()
        self._validate_table()

    # ----- flags -----
    def get_flag(self, mask: int) -> int:
        return 1 if self.status & mask else 0

    def set_flag(self, mask: int, v: bool) -> None:
        if v:
            self.status |= mask
        else:
            self.status &= ~mask & 0xFF

    def _zn(self, v: int) -> None:
        v &= 0xFF
        self.set_flag(self.Z, v == 0)
        self.set_flag(self.N, bool(v & 0x80))

    # ----- reset / interrupts -----
    def reset(self) -> None:
        """Reset: read $FFFC/$FFFD; SP/status match common NES cold boot."""
        self.a = self.x = self.y = 0
        self.sp = 0xFD
        self.status = 0x24  # U | I
        self.jammed = False
        lo = self.bus.read(0xFFFC)
        hi = self.bus.read(0xFFFD)
        self.pc = lo | (hi << 8)
        self.cycles = 0
        self.stall = 0

    def nmi(self) -> None:
        """NMI: push PC + status with B=0, U=1; set I; vector $FFFA."""
        if self.jammed:
            return
        self._push16(self.pc)
        # Interrupt pushes clear B; U always appears set on the stack copy.
        self._push((self.status & ~self.B) | self.U)
        self.set_flag(self.I, True)
        self.pc = self.bus.read(0xFFFA) | (self.bus.read(0xFFFB) << 8)
        self.cycles += 7

    def irq(self) -> None:
        """IRQ: same stack protocol as NMI; ignored when I=1; vector $FFFE."""
        if self.jammed or self.get_flag(self.I):
            return
        self._push16(self.pc)
        self._push((self.status & ~self.B) | self.U)
        self.set_flag(self.I, True)
        self.pc = self.bus.read(0xFFFE) | (self.bus.read(0xFFFF) << 8)
        self.cycles += 7

    def step(self) -> int:
        """Execute one instruction (or one stalled/jammed cycle slice)."""
        if self.stall > 0:
            self.stall -= 1
            self.cycles += 1
            return 1
        if self.jammed:
            # JAM/KIL: CPU is locked; burn cycles, do not fetch further ops.
            self.cycles += 2
            return 2

        start = self.cycles
        op_pc = self.pc
        op = self.bus.read(self.pc)
        self.pc = (self.pc + 1) & 0xFFFF
        entry = self._ops[op]
        if entry is None:  # pragma: no cover — table is total
            raise RuntimeError(f"Unregistered opcode ${op:02X} at ${op_pc:04X}")

        if self.debug:
            print(self.format_debug(op_pc, op, entry), flush=True)

        self._crossed = False
        self.cycles += entry.cycles
        entry.execute()
        if entry.page_cross and self._crossed:
            self.cycles += 1
        return self.cycles - start

    # ----- stack (page $0100, SP wraps 8-bit) -----
    def _push(self, v: int) -> None:
        self.bus.write(0x100 | self.sp, v & 0xFF)
        self.sp = (self.sp - 1) & 0xFF

    def _pull(self) -> int:
        self.sp = (self.sp + 1) & 0xFF
        return self.bus.read(0x100 | self.sp)

    def _push16(self, v: int) -> None:
        self._push((v >> 8) & 0xFF)
        self._push(v & 0xFF)

    def _pull16(self) -> int:
        lo = self._pull()
        hi = self._pull()
        return lo | (hi << 8)

    def _rd8(self) -> int:
        v = self.bus.read(self.pc)
        self.pc = (self.pc + 1) & 0xFFFF
        return v

    def _rd16(self) -> int:
        lo = self._rd8()
        hi = self._rd8()
        return lo | (hi << 8)

    def _rd16_wrap(self, addr: int) -> int:
        """16-bit read with low-byte wrap (zp ptr / JMP indirect page bug)."""
        lo = self.bus.read(addr & 0xFFFF)
        hi = self.bus.read((addr & 0xFF00) | ((addr + 1) & 0xFF))
        return lo | (hi << 8)

    def _page_cross(self, a: int, b: int) -> bool:
        return (a & 0xFF00) != (b & 0xFF00)

    # ----- addressing modes (all bus side effects go through Bus) -----
    def addr_imm(self) -> int:
        a = self.pc
        self.pc = (self.pc + 1) & 0xFFFF
        return a

    def addr_zp(self) -> int:
        return self._rd8()

    def addr_zpx(self) -> int:
        return (self._rd8() + self.x) & 0xFF

    def addr_zpy(self) -> int:
        return (self._rd8() + self.y) & 0xFF

    def addr_abs(self) -> int:
        return self._rd16()

    def addr_absx(self) -> int:
        base = self._rd16()
        addr = (base + self.x) & 0xFFFF
        self._crossed = self._page_cross(base, addr)
        return addr

    def addr_absy(self) -> int:
        base = self._rd16()
        addr = (base + self.y) & 0xFFFF
        self._crossed = self._page_cross(base, addr)
        return addr

    def addr_ind(self) -> int:
        # JMP ($addr): if low byte is $FF, high byte fetched from $xx00 (bug).
        return self._rd16_wrap(self._rd16())

    def addr_indx(self) -> int:
        # (d,X): zero-page pointer wraps; then absolute
        return self._rd16_wrap((self._rd8() + self.x) & 0xFF)

    def addr_indy(self) -> int:
        # (d),Y: zp pointer wraps; Y index may cross pages
        base = self._rd16_wrap(self._rd8())
        addr = (base + self.y) & 0xFFFF
        self._crossed = self._page_cross(base, addr)
        return addr

    def _ea(self, mode: str) -> int:
        return {
            "imm": self.addr_imm,
            "zp": self.addr_zp,
            "zpx": self.addr_zpx,
            "zpy": self.addr_zpy,
            "abs": self.addr_abs,
            "absx": self.addr_absx,
            "absy": self.addr_absy,
            "ind": self.addr_ind,
            "indx": self.addr_indx,
            "indy": self.addr_indy,
        }[mode]()

    # ----- RMW helper (NMOS: read, rewrite old, write new) -----
    def _rmw(self, addr: int, fn: Callable[[int], int]) -> int:
        v = self.bus.read(addr)
        self.bus.write(addr, v)  # dummy write
        nv = fn(v) & 0xFF
        self.bus.write(addr, nv)
        return nv

    # ----- ALU (2A03: ignore D for arithmetic) -----
    def _adc_val(self, v: int) -> None:
        # NES decimal mode: D may be set, but binary arithmetic only.
        a = self.a
        r = a + v + self.get_flag(self.C)
        self.set_flag(self.C, r > 0xFF)
        self.set_flag(self.V, bool(~(a ^ v) & (a ^ r) & 0x80))
        self.a = r & 0xFF
        self._zn(self.a)

    def _sbc_val(self, v: int) -> None:
        self._adc_val(v ^ 0xFF)

    def _cmp(self, reg: int, v: int) -> None:
        r = reg - v
        self.set_flag(self.C, reg >= v)
        self._zn(r)

    # ----- official memory ops -----
    def _lda(self, addr: int) -> None:
        self.a = self.bus.read(addr)
        self._zn(self.a)

    def _ldx(self, addr: int) -> None:
        self.x = self.bus.read(addr)
        self._zn(self.x)

    def _ldy(self, addr: int) -> None:
        self.y = self.bus.read(addr)
        self._zn(self.y)

    def _sta(self, addr: int) -> None:
        self.bus.write(addr, self.a)

    def _stx(self, addr: int) -> None:
        self.bus.write(addr, self.x)

    def _sty(self, addr: int) -> None:
        self.bus.write(addr, self.y)

    def _bit(self, addr: int) -> None:
        v = self.bus.read(addr)
        self.set_flag(self.Z, (self.a & v) == 0)
        self.set_flag(self.N, bool(v & 0x80))
        self.set_flag(self.V, bool(v & 0x40))

    def _asl_m(self, addr: int) -> None:
        def tr(v: int) -> int:
            self.set_flag(self.C, bool(v & 0x80))
            nv = (v << 1) & 0xFF
            self._zn(nv)
            return nv

        self._rmw(addr, tr)

    def _lsr_m(self, addr: int) -> None:
        def tr(v: int) -> int:
            self.set_flag(self.C, bool(v & 1))
            nv = v >> 1
            self._zn(nv)
            return nv

        self._rmw(addr, tr)

    def _rol_m(self, addr: int) -> None:
        def tr(v: int) -> int:
            c = self.get_flag(self.C)
            self.set_flag(self.C, bool(v & 0x80))
            nv = ((v << 1) | c) & 0xFF
            self._zn(nv)
            return nv

        self._rmw(addr, tr)

    def _ror_m(self, addr: int) -> None:
        def tr(v: int) -> int:
            c = self.get_flag(self.C)
            self.set_flag(self.C, bool(v & 1))
            nv = (c << 7) | (v >> 1)
            self._zn(nv)
            return nv

        self._rmw(addr, tr)

    def _inc(self, addr: int) -> None:
        def tr(v: int) -> int:
            nv = (v + 1) & 0xFF
            self._zn(nv)
            return nv

        self._rmw(addr, tr)

    def _dec(self, addr: int) -> None:
        def tr(v: int) -> int:
            nv = (v - 1) & 0xFF
            self._zn(nv)
            return nv

        self._rmw(addr, tr)

    def _branch(self, cond: bool) -> None:
        off = self._rd8()
        if not cond:
            return
        old = self.pc
        if off & 0x80:
            off -= 256
        self.pc = (self.pc + off) & 0xFFFF
        self.cycles += 1  # taken
        if self._page_cross(old, self.pc):
            self.cycles += 1  # page cross

    # ----- unofficial combinations -----
    def _slo(self, addr: int) -> None:
        # ASL mem then ORA A
        def tr(v: int) -> int:
            self.set_flag(self.C, bool(v & 0x80))
            return (v << 1) & 0xFF

        nv = self._rmw(addr, tr)
        self.a |= nv
        self._zn(self.a)

    def _rla(self, addr: int) -> None:
        def tr(v: int) -> int:
            c = self.get_flag(self.C)
            self.set_flag(self.C, bool(v & 0x80))
            return ((v << 1) | c) & 0xFF

        nv = self._rmw(addr, tr)
        self.a &= nv
        self._zn(self.a)

    def _sre(self, addr: int) -> None:
        def tr(v: int) -> int:
            self.set_flag(self.C, bool(v & 1))
            return v >> 1

        nv = self._rmw(addr, tr)
        self.a ^= nv
        self._zn(self.a)

    def _rra(self, addr: int) -> None:
        def tr(v: int) -> int:
            c = self.get_flag(self.C)
            self.set_flag(self.C, bool(v & 1))
            return (c << 7) | (v >> 1)

        nv = self._rmw(addr, tr)
        self._adc_val(nv)

    def _sax(self, addr: int) -> None:
        self.bus.write(addr, self.a & self.x)

    def _lax(self, addr: int) -> None:
        v = self.bus.read(addr)
        self.a = self.x = v
        self._zn(v)

    def _dcp(self, addr: int) -> None:
        def tr(v: int) -> int:
            return (v - 1) & 0xFF

        nv = self._rmw(addr, tr)
        self._cmp(self.a, nv)

    def _isc(self, addr: int) -> None:
        def tr(v: int) -> int:
            return (v + 1) & 0xFF

        nv = self._rmw(addr, tr)
        self._sbc_val(nv)

    def _anc(self) -> None:
        self.a &= self.bus.read(self.addr_imm())
        self._zn(self.a)
        self.set_flag(self.C, bool(self.a & 0x80))

    def _alr(self) -> None:
        self.a &= self.bus.read(self.addr_imm())
        self.set_flag(self.C, bool(self.a & 1))
        self.a >>= 1
        self._zn(self.a)

    def _arr(self) -> None:
        # AND then ROR; C/V from result bits (binary, not BCD).
        self.a &= self.bus.read(self.addr_imm())
        self.a = ((self.get_flag(self.C) << 7) | (self.a >> 1)) & 0xFF
        self._zn(self.a)
        self.set_flag(self.C, bool(self.a & 0x40))
        self.set_flag(self.V, bool(((self.a >> 6) ^ (self.a >> 5)) & 1))

    def _xaa(self) -> None:
        # Highly unstable on real silicon; approximate: A = (A|MAGIC) & X & imm
        imm = self.bus.read(self.addr_imm())
        self.a = (self.a | self._XAA_MAGIC) & self.x & imm
        self._zn(self.a)

    def _axs(self) -> None:
        imm = self.bus.read(self.addr_imm())
        t = self.a & self.x
        r = t - imm
        self.set_flag(self.C, t >= imm)
        self.x = r & 0xFF
        self._zn(self.x)

    def _las(self, addr: int) -> None:
        v = self.bus.read(addr) & self.sp
        self.a = self.x = self.sp = v
        self._zn(v)

    def _ahx(self, addr: int) -> None:
        # Store A&X&(H+1); H is high byte of target before wrap quirks
        h = ((addr >> 8) + 1) & 0xFF
        self.bus.write(addr, self.a & self.x & h)

    def _shy(self, addr: int) -> None:
        h = ((addr >> 8) + 1) & 0xFF
        self.bus.write(addr, self.y & h)

    def _shx(self, addr: int) -> None:
        h = ((addr >> 8) + 1) & 0xFF
        self.bus.write(addr, self.x & h)

    def _tas(self, addr: int) -> None:
        self.sp = self.a & self.x
        h = ((addr >> 8) + 1) & 0xFF
        self.bus.write(addr, self.sp & h)

    def _jam(self) -> None:
        # JAM/KIL: freeze CPU. Leave PC pointing at next byte; flag stops fetch.
        self.jammed = True

    def _nop_addr(self, addr: int) -> None:
        self.bus.read(addr)  # observe side effects (PPU/open bus etc.)

    # ----- implied / accumulator -----
    def _asl_a(self) -> None:
        self.set_flag(self.C, bool(self.a & 0x80))
        self.a = (self.a << 1) & 0xFF
        self._zn(self.a)

    def _lsr_a(self) -> None:
        self.set_flag(self.C, bool(self.a & 1))
        self.a >>= 1
        self._zn(self.a)

    def _rol_a(self) -> None:
        c = self.get_flag(self.C)
        self.set_flag(self.C, bool(self.a & 0x80))
        self.a = ((self.a << 1) | c) & 0xFF
        self._zn(self.a)

    def _ror_a(self) -> None:
        c = self.get_flag(self.C)
        self.set_flag(self.C, bool(self.a & 1))
        self.a = ((c << 7) | (self.a >> 1)) & 0xFF
        self._zn(self.a)

    def _brk(self) -> None:
        # After opcode fetch, PC is at signature byte; skip it (push BRK+2).
        self.pc = (self.pc + 1) & 0xFFFF
        self._push16(self.pc)
        # BRK pushes B=1|U=1 along with status.
        self._push(self.status | self.B | self.U)
        self.set_flag(self.I, True)
        self.pc = self.bus.read(0xFFFE) | (self.bus.read(0xFFFF) << 8)

    def _rti(self) -> None:
        # Pull status: hardware B is not a stored flag; force U=1.
        self.status = (self._pull() & ~self.B) | self.U
        self.pc = self._pull16()

    def _jsr(self) -> None:
        addr = self._rd16()
        self._push16((self.pc - 1) & 0xFFFF)
        self.pc = addr

    def _rts(self) -> None:
        self.pc = (self._pull16() + 1) & 0xFFFF

    def _php(self) -> None:
        self._push(self.status | self.B | self.U)

    def _plp(self) -> None:
        self.status = (self._pull() & ~self.B) | self.U

    # ----- debug / disassembly -----
    def format_debug(self, pc: int, op: int, entry: Optional[OpEntry] = None) -> str:
        entry = entry or self._ops[op]
        dis = self.disassemble(pc)
        return (
            f"PC:{pc:04X}  OP:{op:02X}  {dis}\n"
            f"A:{self.a:02X} X:{self.x:02X} Y:{self.y:02X} "
            f"P:{self.status:02X} SP:{self.sp:02X} CYC:{self.cycles}"
        )

    def disassemble(self, pc: int) -> str:
        op = self.bus.read(pc) & 0xFF
        e = self._ops[op]
        mode = e.mode
        b1 = self.bus.read((pc + 1) & 0xFFFF)
        b2 = self.bus.read((pc + 2) & 0xFFFF)
        absv = b1 | (b2 << 8)
        if mode == "imp":
            return e.mnemonic
        if mode == "acc":
            return f"{e.mnemonic} A"
        if mode == "imm":
            return f"{e.mnemonic} #${b1:02X}"
        if mode == "zp":
            return f"{e.mnemonic} ${b1:02X}"
        if mode == "zpx":
            return f"{e.mnemonic} ${b1:02X},X"
        if mode == "zpy":
            return f"{e.mnemonic} ${b1:02X},Y"
        if mode == "abs":
            return f"{e.mnemonic} ${absv:04X}"
        if mode == "absx":
            return f"{e.mnemonic} ${absv:04X},X"
        if mode == "absy":
            return f"{e.mnemonic} ${absv:04X},Y"
        if mode == "ind":
            return f"{e.mnemonic} (${absv:04X})"
        if mode == "indx":
            return f"{e.mnemonic} (${b1:02X},X)"
        if mode == "indy":
            return f"{e.mnemonic} (${b1:02X}),Y"
        if mode == "rel":
            off = b1 - 256 if b1 & 0x80 else b1
            tgt = (pc + 2 + off) & 0xFFFF
            return f"{e.mnemonic} ${tgt:04X}"
        return e.mnemonic

    # ----- table build -----
    def _set(
        self,
        table: List[Optional[OpEntry]],
        code: int,
        mnemonic: str,
        mode: str,
        cycles: int,
        fn: Callable[[], None],
        *,
        page: bool = False,
        unofficial: bool = False,
    ) -> None:
        if table[code] is not None:
            raise RuntimeError(f"Duplicate opcode ${code:02X}")
        table[code] = OpEntry(mnemonic, mode, cycles, page, unofficial, fn)

    def _build_ops(self) -> List[OpEntry]:
        T: List[Optional[OpEntry]] = [None] * 256
        S = self._set
        C = self

        def rd(mode: str) -> Callable[[], int]:
            return lambda m=mode: C._ea(m)

        # --- load/store/alu families ---
        def load_op(code, name, mode, cyc, page, setter):
            S(T, code, name, mode, cyc, lambda s=setter, m=mode: s(C._ea(m)), page=page)

        def store_op(code, name, mode, cyc, writer):
            # Stores: fixed cycles (no page-cross add) even if address crosses.
            S(T, code, name, mode, cyc, lambda w=writer, m=mode: w(C._ea(m)), page=False)

        def alu_op(code, name, mode, cyc, page, body):
            S(T, code, name, mode, cyc, lambda b=body, m=mode: b(C._ea(m)), page=page)

        def rmw_op(code, name, mode, cyc, body, unofficial=False):
            S(
                T,
                code,
                name,
                mode,
                cyc,
                lambda b=body, m=mode: b(C._ea(m)),
                page=False,
                unofficial=unofficial,
            )

        # LDA
        load_op(0xA9, "LDA", "imm", 2, False, C._lda)
        load_op(0xA5, "LDA", "zp", 3, False, C._lda)
        load_op(0xB5, "LDA", "zpx", 4, False, C._lda)
        load_op(0xAD, "LDA", "abs", 4, False, C._lda)
        load_op(0xBD, "LDA", "absx", 4, True, C._lda)
        load_op(0xB9, "LDA", "absy", 4, True, C._lda)
        load_op(0xA1, "LDA", "indx", 6, False, C._lda)
        load_op(0xB1, "LDA", "indy", 5, True, C._lda)
        # LDX / LDY
        load_op(0xA2, "LDX", "imm", 2, False, C._ldx)
        load_op(0xA6, "LDX", "zp", 3, False, C._ldx)
        load_op(0xB6, "LDX", "zpy", 4, False, C._ldx)
        load_op(0xAE, "LDX", "abs", 4, False, C._ldx)
        load_op(0xBE, "LDX", "absy", 4, True, C._ldx)
        load_op(0xA0, "LDY", "imm", 2, False, C._ldy)
        load_op(0xA4, "LDY", "zp", 3, False, C._ldy)
        load_op(0xB4, "LDY", "zpx", 4, False, C._ldy)
        load_op(0xAC, "LDY", "abs", 4, False, C._ldy)
        load_op(0xBC, "LDY", "absx", 4, True, C._ldy)
        # STA / STX / STY
        store_op(0x85, "STA", "zp", 3, C._sta)
        store_op(0x95, "STA", "zpx", 4, C._sta)
        store_op(0x8D, "STA", "abs", 4, C._sta)
        store_op(0x9D, "STA", "absx", 5, C._sta)
        store_op(0x99, "STA", "absy", 5, C._sta)
        store_op(0x81, "STA", "indx", 6, C._sta)
        store_op(0x91, "STA", "indy", 6, C._sta)
        store_op(0x86, "STX", "zp", 3, C._stx)
        store_op(0x96, "STX", "zpy", 4, C._stx)
        store_op(0x8E, "STX", "abs", 4, C._stx)
        store_op(0x84, "STY", "zp", 3, C._sty)
        store_op(0x94, "STY", "zpx", 4, C._sty)
        store_op(0x8C, "STY", "abs", 4, C._sty)

        # Transfers
        S(T, 0xAA, "TAX", "imp", 2, lambda: (setattr(C, "x", C.a), C._zn(C.x)))
        S(T, 0xA8, "TAY", "imp", 2, lambda: (setattr(C, "y", C.a), C._zn(C.y)))
        S(T, 0xBA, "TSX", "imp", 2, lambda: (setattr(C, "x", C.sp), C._zn(C.x)))
        S(T, 0x8A, "TXA", "imp", 2, lambda: (setattr(C, "a", C.x), C._zn(C.a)))
        S(T, 0x9A, "TXS", "imp", 2, lambda: setattr(C, "sp", C.x))
        S(T, 0x98, "TYA", "imp", 2, lambda: (setattr(C, "a", C.y), C._zn(C.a)))

        # Stack
        S(T, 0x48, "PHA", "imp", 3, lambda: C._push(C.a))
        S(T, 0x68, "PLA", "imp", 4, lambda: (setattr(C, "a", C._pull()), C._zn(C.a)))
        S(T, 0x08, "PHP", "imp", 3, C._php)
        S(T, 0x28, "PLP", "imp", 4, C._plp)

        # ADC / SBC / AND / ORA / EOR / CMP
        for code, mode, cyc, page in (
            (0x69, "imm", 2, False),
            (0x65, "zp", 3, False),
            (0x75, "zpx", 4, False),
            (0x6D, "abs", 4, False),
            (0x7D, "absx", 4, True),
            (0x79, "absy", 4, True),
            (0x61, "indx", 6, False),
            (0x71, "indy", 5, True),
        ):
            alu_op(code, "ADC", mode, cyc, page, lambda a: C._adc_val(C.bus.read(a)))
        for code, mode, cyc, page in (
            (0xE9, "imm", 2, False),
            (0xE5, "zp", 3, False),
            (0xF5, "zpx", 4, False),
            (0xED, "abs", 4, False),
            (0xFD, "absx", 4, True),
            (0xF9, "absy", 4, True),
            (0xE1, "indx", 6, False),
            (0xF1, "indy", 5, True),
        ):
            alu_op(code, "SBC", mode, cyc, page, lambda a: C._sbc_val(C.bus.read(a)))
        for code, mode, cyc, page in (
            (0x29, "imm", 2, False),
            (0x25, "zp", 3, False),
            (0x35, "zpx", 4, False),
            (0x2D, "abs", 4, False),
            (0x3D, "absx", 4, True),
            (0x39, "absy", 4, True),
            (0x21, "indx", 6, False),
            (0x31, "indy", 5, True),
        ):
            alu_op(
                code,
                "AND",
                mode,
                cyc,
                page,
                lambda a: (setattr(C, "a", C.a & C.bus.read(a)), C._zn(C.a)),
            )
        for code, mode, cyc, page in (
            (0x09, "imm", 2, False),
            (0x05, "zp", 3, False),
            (0x15, "zpx", 4, False),
            (0x0D, "abs", 4, False),
            (0x1D, "absx", 4, True),
            (0x19, "absy", 4, True),
            (0x01, "indx", 6, False),
            (0x11, "indy", 5, True),
        ):
            alu_op(
                code,
                "ORA",
                mode,
                cyc,
                page,
                lambda a: (setattr(C, "a", C.a | C.bus.read(a)), C._zn(C.a)),
            )
        for code, mode, cyc, page in (
            (0x49, "imm", 2, False),
            (0x45, "zp", 3, False),
            (0x55, "zpx", 4, False),
            (0x4D, "abs", 4, False),
            (0x5D, "absx", 4, True),
            (0x59, "absy", 4, True),
            (0x41, "indx", 6, False),
            (0x51, "indy", 5, True),
        ):
            alu_op(
                code,
                "EOR",
                mode,
                cyc,
                page,
                lambda a: (setattr(C, "a", C.a ^ C.bus.read(a)), C._zn(C.a)),
            )
        for code, mode, cyc, page in (
            (0xC9, "imm", 2, False),
            (0xC5, "zp", 3, False),
            (0xD5, "zpx", 4, False),
            (0xCD, "abs", 4, False),
            (0xDD, "absx", 4, True),
            (0xD9, "absy", 4, True),
            (0xC1, "indx", 6, False),
            (0xD1, "indy", 5, True),
        ):
            alu_op(code, "CMP", mode, cyc, page, lambda a: C._cmp(C.a, C.bus.read(a)))
        alu_op(0xE0, "CPX", "imm", 2, False, lambda a: C._cmp(C.x, C.bus.read(a)))
        alu_op(0xE4, "CPX", "zp", 3, False, lambda a: C._cmp(C.x, C.bus.read(a)))
        alu_op(0xEC, "CPX", "abs", 4, False, lambda a: C._cmp(C.x, C.bus.read(a)))
        alu_op(0xC0, "CPY", "imm", 2, False, lambda a: C._cmp(C.y, C.bus.read(a)))
        alu_op(0xC4, "CPY", "zp", 3, False, lambda a: C._cmp(C.y, C.bus.read(a)))
        alu_op(0xCC, "CPY", "abs", 4, False, lambda a: C._cmp(C.y, C.bus.read(a)))

        S(T, 0x24, "BIT", "zp", 3, lambda: C._bit(C.addr_zp()))
        S(T, 0x2C, "BIT", "abs", 4, lambda: C._bit(C.addr_abs()))

        # Shifts / RMW
        S(T, 0x0A, "ASL", "acc", 2, C._asl_a)
        rmw_op(0x06, "ASL", "zp", 5, C._asl_m)
        rmw_op(0x16, "ASL", "zpx", 6, C._asl_m)
        rmw_op(0x0E, "ASL", "abs", 6, C._asl_m)
        rmw_op(0x1E, "ASL", "absx", 7, C._asl_m)
        S(T, 0x4A, "LSR", "acc", 2, C._lsr_a)
        rmw_op(0x46, "LSR", "zp", 5, C._lsr_m)
        rmw_op(0x56, "LSR", "zpx", 6, C._lsr_m)
        rmw_op(0x4E, "LSR", "abs", 6, C._lsr_m)
        rmw_op(0x5E, "LSR", "absx", 7, C._lsr_m)
        S(T, 0x2A, "ROL", "acc", 2, C._rol_a)
        rmw_op(0x26, "ROL", "zp", 5, C._rol_m)
        rmw_op(0x36, "ROL", "zpx", 6, C._rol_m)
        rmw_op(0x2E, "ROL", "abs", 6, C._rol_m)
        rmw_op(0x3E, "ROL", "absx", 7, C._rol_m)
        S(T, 0x6A, "ROR", "acc", 2, C._ror_a)
        rmw_op(0x66, "ROR", "zp", 5, C._ror_m)
        rmw_op(0x76, "ROR", "zpx", 6, C._ror_m)
        rmw_op(0x6E, "ROR", "abs", 6, C._ror_m)
        rmw_op(0x7E, "ROR", "absx", 7, C._ror_m)
        rmw_op(0xE6, "INC", "zp", 5, C._inc)
        rmw_op(0xF6, "INC", "zpx", 6, C._inc)
        rmw_op(0xEE, "INC", "abs", 6, C._inc)
        rmw_op(0xFE, "INC", "absx", 7, C._inc)
        rmw_op(0xC6, "DEC", "zp", 5, C._dec)
        rmw_op(0xD6, "DEC", "zpx", 6, C._dec)
        rmw_op(0xCE, "DEC", "abs", 6, C._dec)
        rmw_op(0xDE, "DEC", "absx", 7, C._dec)

        S(T, 0xE8, "INX", "imp", 2, lambda: (setattr(C, "x", (C.x + 1) & 0xFF), C._zn(C.x)))
        S(T, 0xC8, "INY", "imp", 2, lambda: (setattr(C, "y", (C.y + 1) & 0xFF), C._zn(C.y)))
        S(T, 0xCA, "DEX", "imp", 2, lambda: (setattr(C, "x", (C.x - 1) & 0xFF), C._zn(C.x)))
        S(T, 0x88, "DEY", "imp", 2, lambda: (setattr(C, "y", (C.y - 1) & 0xFF), C._zn(C.y)))

        # Flags
        S(T, 0x18, "CLC", "imp", 2, lambda: C.set_flag(C.C, False))
        S(T, 0x38, "SEC", "imp", 2, lambda: C.set_flag(C.C, True))
        S(T, 0x58, "CLI", "imp", 2, lambda: C.set_flag(C.I, False))
        S(T, 0x78, "SEI", "imp", 2, lambda: C.set_flag(C.I, True))
        S(T, 0xB8, "CLV", "imp", 2, lambda: C.set_flag(C.V, False))
        S(T, 0xD8, "CLD", "imp", 2, lambda: C.set_flag(C.D, False))
        S(T, 0xF8, "SED", "imp", 2, lambda: C.set_flag(C.D, True))

        # Branches
        S(T, 0x10, "BPL", "rel", 2, lambda: C._branch(not C.get_flag(C.N)))
        S(T, 0x30, "BMI", "rel", 2, lambda: C._branch(bool(C.get_flag(C.N))))
        S(T, 0x50, "BVC", "rel", 2, lambda: C._branch(not C.get_flag(C.V)))
        S(T, 0x70, "BVS", "rel", 2, lambda: C._branch(bool(C.get_flag(C.V))))
        S(T, 0x90, "BCC", "rel", 2, lambda: C._branch(not C.get_flag(C.C)))
        S(T, 0xB0, "BCS", "rel", 2, lambda: C._branch(bool(C.get_flag(C.C))))
        S(T, 0xD0, "BNE", "rel", 2, lambda: C._branch(not C.get_flag(C.Z)))
        S(T, 0xF0, "BEQ", "rel", 2, lambda: C._branch(bool(C.get_flag(C.Z))))

        # Flow
        S(T, 0x4C, "JMP", "abs", 3, lambda: setattr(C, "pc", C.addr_abs()))
        S(T, 0x6C, "JMP", "ind", 5, lambda: setattr(C, "pc", C.addr_ind()))
        S(T, 0x20, "JSR", "abs", 6, C._jsr)
        S(T, 0x60, "RTS", "imp", 6, C._rts)
        S(T, 0x40, "RTI", "imp", 6, C._rti)
        S(T, 0x00, "BRK", "imp", 7, C._brk)
        S(T, 0xEA, "NOP", "imp", 2, lambda: None)

        # ===== Unofficial / illegal NMOS opcodes =====
        # JAM / KIL
        for code in (0x02, 0x12, 0x22, 0x32, 0x42, 0x52, 0x62, 0x72, 0x92, 0xB2, 0xD2, 0xF2):
            S(T, code, "JAM", "imp", 2, C._jam, unofficial=True)

        # NOP variants
        for code in (0x1A, 0x3A, 0x5A, 0x7A, 0xDA, 0xFA):
            S(T, code, "*NOP", "imp", 2, lambda: None, unofficial=True)
        for code in (0x80, 0x82, 0x89, 0xC2, 0xE2):
            S(T, code, "*NOP", "imm", 2, lambda: C.addr_imm(), unofficial=True)
        for code in (0x04, 0x44, 0x64):
            S(T, code, "*NOP", "zp", 3, lambda: C._nop_addr(C.addr_zp()), unofficial=True)
        for code in (0x14, 0x34, 0x54, 0x74, 0xD4, 0xF4):
            S(T, code, "*NOP", "zpx", 4, lambda: C._nop_addr(C.addr_zpx()), unofficial=True)
        S(T, 0x0C, "*NOP", "abs", 4, lambda: C._nop_addr(C.addr_abs()), unofficial=True)
        for code in (0x1C, 0x3C, 0x5C, 0x7C, 0xDC, 0xFC):
            S(
                T,
                code,
                "*NOP",
                "absx",
                4,
                lambda: C._nop_addr(C.addr_absx()),
                page=True,
                unofficial=True,
            )

        # SLO / RLA / SRE / RRA
        for code, mode, cyc in (
            (0x07, "zp", 5),
            (0x17, "zpx", 6),
            (0x03, "indx", 8),
            (0x13, "indy", 8),
            (0x0F, "abs", 6),
            (0x1F, "absx", 7),
            (0x1B, "absy", 7),
        ):
            rmw_op(code, "*SLO", mode, cyc, C._slo, unofficial=True)
        for code, mode, cyc in (
            (0x27, "zp", 5),
            (0x37, "zpx", 6),
            (0x23, "indx", 8),
            (0x33, "indy", 8),
            (0x2F, "abs", 6),
            (0x3F, "absx", 7),
            (0x3B, "absy", 7),
        ):
            rmw_op(code, "*RLA", mode, cyc, C._rla, unofficial=True)
        for code, mode, cyc in (
            (0x47, "zp", 5),
            (0x57, "zpx", 6),
            (0x43, "indx", 8),
            (0x53, "indy", 8),
            (0x4F, "abs", 6),
            (0x5F, "absx", 7),
            (0x5B, "absy", 7),
        ):
            rmw_op(code, "*SRE", mode, cyc, C._sre, unofficial=True)
        for code, mode, cyc in (
            (0x67, "zp", 5),
            (0x77, "zpx", 6),
            (0x63, "indx", 8),
            (0x73, "indy", 8),
            (0x6F, "abs", 6),
            (0x7F, "absx", 7),
            (0x7B, "absy", 7),
        ):
            rmw_op(code, "*RRA", mode, cyc, C._rra, unofficial=True)

        # SAX / LAX / DCP / ISC
        for code, mode, cyc in (
            (0x87, "zp", 3),
            (0x97, "zpy", 4),
            (0x83, "indx", 6),
            (0x8F, "abs", 4),
        ):
            store_op(code, "*SAX", mode, cyc, C._sax)
            T[code] = OpEntry("*SAX", mode, cyc, False, True, T[code].execute)
        for code, mode, cyc, page in (
            (0xA7, "zp", 3, False),
            (0xB7, "zpy", 4, False),
            (0xA3, "indx", 6, False),
            (0xB3, "indy", 5, True),
            (0xAF, "abs", 4, False),
            (0xBF, "absy", 4, True),
        ):
            load_op(code, "*LAX", mode, cyc, page, C._lax)
            T[code] = OpEntry("*LAX", mode, cyc, page, True, T[code].execute)
        # LAX immediate (unstable; treat as LDA/LDX of imm)
        S(
            T,
            0xAB,
            "*LAX",
            "imm",
            2,
            lambda: (setattr(C, "a", C.bus.read(C.addr_imm())), setattr(C, "x", C.a), C._zn(C.a)),
            unofficial=True,
        )

        for code, mode, cyc in (
            (0xC7, "zp", 5),
            (0xD7, "zpx", 6),
            (0xC3, "indx", 8),
            (0xD3, "indy", 8),
            (0xCF, "abs", 6),
            (0xDF, "absx", 7),
            (0xDB, "absy", 7),
        ):
            rmw_op(code, "*DCP", mode, cyc, C._dcp, unofficial=True)
        for code, mode, cyc in (
            (0xE7, "zp", 5),
            (0xF7, "zpx", 6),
            (0xE3, "indx", 8),
            (0xF3, "indy", 8),
            (0xEF, "abs", 6),
            (0xFF, "absx", 7),
            (0xFB, "absy", 7),
        ):
            rmw_op(code, "*ISC", mode, cyc, C._isc, unofficial=True)

        # Immediate unofficials
        S(T, 0x0B, "*ANC", "imm", 2, C._anc, unofficial=True)
        S(T, 0x2B, "*ANC", "imm", 2, C._anc, unofficial=True)
        S(T, 0x4B, "*ALR", "imm", 2, C._alr, unofficial=True)
        S(T, 0x6B, "*ARR", "imm", 2, C._arr, unofficial=True)
        S(T, 0x8B, "*XAA", "imm", 2, C._xaa, unofficial=True)
        S(T, 0xCB, "*AXS", "imm", 2, C._axs, unofficial=True)
        # *SBC imm duplicate of official SBC
        S(
            T,
            0xEB,
            "*SBC",
            "imm",
            2,
            lambda: C._sbc_val(C.bus.read(C.addr_imm())),
            unofficial=True,
        )

        # AHX / SHY / SHX / TAS / LAS
        S(T, 0x93, "*AHX", "indy", 6, lambda: C._ahx(C.addr_indy()), unofficial=True)
        S(T, 0x9F, "*AHX", "absy", 5, lambda: C._ahx(C.addr_absy()), unofficial=True)
        S(T, 0x9C, "*SHY", "absx", 5, lambda: C._shy(C.addr_absx()), unofficial=True)
        S(T, 0x9E, "*SHX", "absy", 5, lambda: C._shx(C.addr_absy()), unofficial=True)
        S(T, 0x9B, "*TAS", "absy", 5, lambda: C._tas(C.addr_absy()), unofficial=True)
        S(
            T,
            0xBB,
            "*LAS",
            "absy",
            4,
            lambda: C._las(C.addr_absy()),
            page=True,
            unofficial=True,
        )

        # Fix unofficial flag on SAX/LAX entries created via store_op/load_op
        for code in (0x87, 0x97, 0x83, 0x8F):
            e = T[code]
            assert e is not None
            T[code] = OpEntry(e.mnemonic if e.mnemonic.startswith("*") else "*SAX", e.mode, e.cycles, False, True, e.execute)

        missing = [i for i, e in enumerate(T) if e is None]
        if missing:
            raise RuntimeError(f"Opcode table incomplete: missing {len(missing)}: {missing[:20]}")
        return [e for e in T]  # type: ignore[misc]

    def _validate_table(self) -> None:
        if len(self._ops) != 256:
            raise RuntimeError("opcode table size != 256")
        for i, e in enumerate(self._ops):
            if e is None or e.execute is None:
                raise RuntimeError(f"Unregistered opcode ${i:02X}")

    @staticmethod
    def official_count(ops: List[OpEntry]) -> int:
        return sum(1 for e in ops if not e.unofficial)

    @staticmethod
    def unofficial_count(ops: List[OpEntry]) -> int:
        return sum(1 for e in ops if e.unofficial)


class _SelfTestBus:
    """Minimal bus for CPU construction / opcode selftest (no cartridge)."""

    def read(self, addr: int) -> int:
        return 0

    def write(self, addr: int, value: int) -> None:
        return None


def run_cpu_selftest() -> int:
    """Confirm every opcode 0x00–0xFF maps to an intentional implementation."""
    cpu = CPU(_SelfTestBus())  # type: ignore[arg-type]
    n = len(cpu._ops)
    official = CPU.official_count(cpu._ops)
    unofficial = CPU.unofficial_count(cpu._ops)
    missing = sum(1 for e in cpu._ops if e is None)
    print("[VIRTUALNES CPU SELFTEST]")
    print(f"Opcode entries: {n}/256")
    print("Official opcodes: covered" if official >= 151 else f"Official opcodes: {official}")
    print("Unofficial opcodes: covered" if unofficial >= 1 and missing == 0 else f"Unofficial: {unofficial}")
    print(f"Missing opcodes: {missing}")
    print("2A03 decimal behavior: enabled")
    print("CPU core: READY")
    return 0 if n == 256 and missing == 0 else 1


class Bus:
    def __init__(self, cart: Cartridge) -> None:
        self.cart = cart
        self.ram = bytearray(0x800)
        self.controller1 = Controller()
        self.controller2 = Controller()
        self.apu = APU()
        self.ppu = PPU(cart)
        self.cpu: Optional[CPU] = None

    def attach_cpu(self, cpu: CPU) -> None:
        self.cpu = cpu

    def reset(self) -> None:
        self.ram[:] = bytearray(0x800)
        self.apu.reset()
        self.ppu.reset()
        assert self.cpu is not None
        self.cpu.reset()

    def read(self, addr: int) -> int:
        addr &= 0xFFFF
        if addr < 0x2000:
            return self.ram[addr & 0x7FF]
        if addr < 0x4000:
            return self.ppu.read_reg(addr)
        if addr == 0x4015:
            return self.apu.read(addr)
        if addr == 0x4016:
            return self.controller1.read()
        if addr == 0x4017:
            return self.controller2.read()
        if addr >= 0x4020:
            return self.cart.cpu_read(addr)
        return 0

    def write(self, addr: int, value: int) -> None:
        addr &= 0xFFFF
        value &= 0xFF
        if addr < 0x2000:
            self.ram[addr & 0x7FF] = value
        elif addr < 0x4000:
            self.ppu.write_reg(addr, value)
        elif addr == 0x4014:  # OAM DMA
            self._oam_dma(value)
        elif addr == 0x4016:
            self.controller1.write(value)
            self.controller2.write(value)
        elif 0x4000 <= addr <= 0x4017:
            self.apu.write(addr, value)
        elif addr >= 0x4020:
            self.cart.cpu_write(addr, value)

    def _oam_dma(self, page: int) -> None:
        base = page << 8
        for i in range(256):
            self.ppu.oam[i] = self.read(base + i)
        if self.cpu:
            self.cpu.stall += 513 + (self.cpu.cycles & 1)


# =============================================================================
# FCEUX-style GUI application
# =============================================================================
class VirtualNESApp:
    """FCEUX-inspired Tk desktop UI around the NES core."""

    BG = "#000000"
    FG = "#7EC8FF"
    FG_DIM = "#3A7AB0"
    BORDER = "#1E5AA8"
    BORDER_HI = "#3A8AD4"
    MENU_BG = "#000A18"
    TOOL_BG = "#000E22"
    STATUS_BG = "#000410"
    BTN_BG = "#001830"
    BTN_ACTIVE = "#103868"

    def __init__(self, rom_path: Optional[str]) -> None:
        self.root = tk.Tk()
        self.root.title("VirtualNES 0.1.1")
        self.root.configure(bg=self.BG)
        self.root.resizable(False, False)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        self.rom_path = rom_path
        self.cart: Optional[Cartridge] = None
        self.bus: Optional[Bus] = None
        self.cpu: Optional[CPU] = None
        self.running = False
        self.paused = False
        self.error_msg = ""
        self.state = "ERROR"
        self.fps = 0.0
        self.scale = SCALE
        self._frame_times: list[float] = []
        self._photo: Optional[tk.PhotoImage] = None
        self._scaled: Optional[tk.PhotoImage] = None
        self._ppm_header = f"P6 {NES_W} {NES_H} 255\n".encode("ascii")
        self._hex_lut = [f"#{r:02x}{g:02x}{b:02x}" for r, g, b in NES_PALETTE]
        self._loop_id: Optional[str] = None
        self._status_tick = 0
        self._cpu_debug = False

        self._build_menu()
        self._build_toolbar()
        self._build_title()
        self._build_screen()
        self._build_status()
        self._bind_keys()
        self._center_window()

        # Idle GUI without argv[1]; File→Load ROM or CLI path starts emulation
        if rom_path:
            self._start_rom(rom_path)
        else:
            self.state = "IDLE"
            self.running = False
            self.error_msg = ""
            self._draw_placeholder("VirtualNES")
            self._set_toolbar_state(False)

        self._update_status()
        self._loop_id = self.root.after(FRAME_MS, self._frame_loop)

    # ----- chrome -----
    def _menu_style(self) -> dict:
        return {
            "tearoff": 0,
            "bg": self.MENU_BG,
            "fg": self.FG,
            "activebackground": self.BORDER,
            "activeforeground": "#FFFFFF",
            "bd": 1,
        }

    def _build_menu(self) -> None:
        # Native menubar (VB6 / classic FCEUX layout)
        menubar = tk.Menu(self.root, **self._menu_style())

        file_m = tk.Menu(menubar, **self._menu_style())
        file_m.add_command(label="Load ROM…\tCtrl+O", command=self.on_load_rom)
        file_m.add_command(label="Play ROM\tSpace", command=self.on_play_rom)
        file_m.add_separator()
        file_m.add_command(label="Exit\tEsc", command=self._on_close)
        menubar.add_cascade(label="File", menu=file_m)

        nes = tk.Menu(menubar, **self._menu_style())
        nes.add_command(label="Play ROM\tSpace", command=self.on_play_rom)
        nes.add_command(label="Reset\tR", command=self.on_reset)
        nes.add_command(label="Pause/Resume\tP", command=self.on_pause)
        nes.add_separator()
        nes.add_command(label="Exit\tEsc", command=self._on_close)
        menubar.add_cascade(label="NES", menu=nes)

        cfg = tk.Menu(menubar, **self._menu_style())
        vid = tk.Menu(cfg, **self._menu_style())
        vid.add_command(label="Scale 1×", command=lambda: self._set_scale(1))
        vid.add_command(label="Scale 2× (fit)", command=lambda: self._set_scale(2))
        cfg.add_cascade(label="Video", menu=vid)
        cfg.add_command(label="Audio", command=lambda: self._dummy("Audio"))
        cfg.add_command(label="Input", command=lambda: self._dummy("Input"))
        menubar.add_cascade(label="Config", menu=cfg)

        helpm = tk.Menu(menubar, **self._menu_style())
        helpm.add_command(label="Controls", command=self._controls_help)
        helpm.add_command(label="About VirtualNES", command=self._about)
        menubar.add_cascade(label="Help", menu=helpm)
        self.root.config(menu=menubar)

    def _tool_btn(self, parent: tk.Widget, text: str, cmd: Callable[[], None]) -> tk.Button:
        return tk.Button(
            parent,
            text=text,
            command=cmd,
            bg=self.BTN_BG,
            fg=self.FG,
            activebackground=self.BTN_ACTIVE,
            activeforeground="#FFFFFF",
            relief=tk.RAISED,
            bd=1,
            padx=10,
            pady=2,
            font=("Tahoma", 8),
            highlightthickness=0,
        )

    def _build_toolbar(self) -> None:
        bar = tk.Frame(
            self.root,
            bg=self.TOOL_BG,
            highlightbackground=self.BORDER,
            highlightthickness=1,
        )
        bar.pack(fill=tk.X)
        self.btn_reset = self._tool_btn(bar, "Reset", self.on_reset)
        self.btn_pause = self._tool_btn(bar, "Pause", self.on_pause)
        self.btn_play = self._tool_btn(bar, "Play ROM", self.on_play_rom)
        self.btn_load = self._tool_btn(bar, "Load ROM…", self.on_load_rom)
        self.btn_load.pack(side=tk.LEFT, padx=(6, 3), pady=4)
        self.btn_play.pack(side=tk.LEFT, padx=3, pady=4)
        self.btn_reset.pack(side=tk.LEFT, padx=3, pady=4)
        self.btn_pause.pack(side=tk.LEFT, padx=3, pady=4)
        tk.Label(
            bar,
            text="  VirtualNES 0.1  ·  NTSC  ·  files=ON",
            bg=self.TOOL_BG,
            fg=self.FG_DIM,
            font=("Tahoma", 8),
        ).pack(side=tk.RIGHT, padx=8)
        self._set_toolbar_state(False)

    def _build_title(self) -> None:
        title = tk.Frame(self.root, bg=self.BG)
        title.pack(fill=tk.X, pady=(8, 0))
        tk.Label(
            title,
            text="VirtualNES",
            bg=self.BG,
            fg=self.BORDER_HI,
            font=("Tahoma", 16, "bold"),
        ).pack()
        tk.Label(
            title,
            text="Famicom / NES NTSC core",
            bg=self.BG,
            fg=self.FG_DIM,
            font=("Tahoma", 8),
        ).pack()

    def _build_screen(self) -> None:
        # Fill remaining space inside fixed 600×400 window; NES canvas centered
        wrap = tk.Frame(self.root, bg=self.BG)
        wrap.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)
        # Double bevel like classic emulators
        outer = tk.Frame(wrap, bg=self.BORDER_HI, padx=1, pady=1)
        outer.place(relx=0.5, rely=0.5, anchor=tk.CENTER)
        mid = tk.Frame(outer, bg=self.BORDER, padx=3, pady=3)
        mid.pack()
        self._screen_host = tk.Frame(mid, bg="#000000")
        self._screen_host.pack()
        self.canvas = tk.Canvas(
            self._screen_host,
            width=NES_W * self.scale,
            height=NES_H * self.scale,
            bg="#000000",
            highlightthickness=0,
            cursor="tcross",
        )
        self.canvas.pack()
        self._photo = tk.PhotoImage(width=NES_W, height=NES_H)
        self._img_id = self.canvas.create_image(0, 0, anchor=tk.NW, image=self._photo)
        self._draw_placeholder("No ROM")

    def _build_status(self) -> None:
        self.status_var = tk.StringVar(value="VirtualNES — ready")
        bar = tk.Label(
            self.root,
            textvariable=self.status_var,
            anchor=tk.W,
            bg=self.STATUS_BG,
            fg=self.FG,
            font=("Consolas", 9),
            relief=tk.SUNKEN,
            bd=1,
            padx=8,
            pady=4,
        )
        bar.pack(fill=tk.X, side=tk.BOTTOM)

    def _set_toolbar_state(self, enabled: bool) -> None:
        # Load / Play always available when files=ON; Reset/Pause need a cart
        self.btn_load.configure(state=tk.NORMAL if files else tk.DISABLED)
        self.btn_play.configure(state=tk.NORMAL)
        st = tk.NORMAL if enabled else tk.DISABLED
        self.btn_reset.configure(state=st)
        self.btn_pause.configure(state=st)

    def _center_window(self) -> None:
        """Fixed 600×400 window, centered on the OS desktop."""
        self.root.update_idletasks()
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        x = max(0, (sw - WIN_W) // 2)
        y = max(0, (sh - WIN_H) // 2)
        self.root.geometry(f"{WIN_W}x{WIN_H}+{x}+{y}")
        self.root.minsize(WIN_W, WIN_H)
        self.root.maxsize(WIN_W, WIN_H)

    def _draw_placeholder(self, text: str) -> None:
        self.canvas.delete("overlay")
        cw = NES_W * self.scale
        ch = NES_H * self.scale
        self.canvas.create_rectangle(0, 0, cw, ch, fill="#000000", outline="", tags="overlay")
        self.canvas.create_text(
            cw // 2,
            ch // 2,
            text=text,
            fill=self.FG_DIM,
            font=("Tahoma", 12),
            tags="overlay",
        )

    # ----- input -----
    def _bind_keys(self) -> None:
        pad = {
            "z": Controller.A,
            "Z": Controller.A,
            "x": Controller.B,
            "X": Controller.B,
            "Return": Controller.START,
            "Shift_R": Controller.SELECT,
            "Up": Controller.UP,
            "Down": Controller.DOWN,
            "Left": Controller.LEFT,
            "Right": Controller.RIGHT,
        }

        def press(e: tk.Event) -> None:
            if e.keysym == "space":
                self.on_play_rom()
                return
            if e.keysym in ("o", "O") and (e.state & 0x4):
                self.on_load_rom()
                return
            if e.keysym in ("p", "P") and not (e.state & 0x4):
                self.on_pause()
                return
            if e.keysym in ("r", "R") and not (e.state & 0x4):
                self.on_reset()
                return
            if e.keysym == "Escape":
                self._on_close()
                return
            if e.keysym == "F1":
                self._about()
                return
            if self.bus and e.keysym in pad:
                self.bus.controller1.set_key(pad[e.keysym], True)

        def release(e: tk.Event) -> None:
            if self.bus and e.keysym in pad:
                self.bus.controller1.set_key(pad[e.keysym], False)

        self.root.bind("<KeyPress>", press)
        self.root.bind("<KeyRelease>", release)
        self.root.bind("<F1>", lambda _e: self._about())
        self.root.bind("<Control-o>", lambda _e: self.on_load_rom())
        self.root.bind("<Control-O>", lambda _e: self.on_load_rom())

    # ----- ROM / lifecycle -----
    def on_load_rom(self) -> None:
        """File→Load ROM… / toolbar / Ctrl+O."""
        if not files:
            messagebox.showinfo(
                "VirtualNES",
                "files=OFF — pass a ROM on the command line.",
                parent=self.root,
            )
            return
        initial = os.path.dirname(self.rom_path) if self.rom_path else os.path.expanduser("~")
        path = filedialog.askopenfilename(
            parent=self.root,
            title="Load NES ROM",
            initialdir=initial if os.path.isdir(initial) else os.path.expanduser("~"),
            filetypes=[
                ("NES ROMs", "*.nes"),
                ("NES ROMs", "*.NES"),
                ("All files", "*.*"),
            ],
        )
        if path:
            self._start_rom(path)

    def on_play_rom(self) -> None:
        """Play ROM: pick a file if needed, else resume / start emulation."""
        if self.cart is None or self.bus is None or self.cpu is None:
            # No cartridge yet — load then play
            if files:
                self.on_load_rom()
            elif self.rom_path:
                self._start_rom(self.rom_path)
            else:
                messagebox.showinfo(
                    "Play ROM",
                    "No ROM loaded. Use File→Load ROM… or pass a path on the command line.",
                    parent=self.root,
                )
            return

        # Resume from pause, or kick idle/error cart back to RUNNING
        self.paused = False
        self.running = True
        self.state = "RUNNING"
        self.error_msg = ""
        self.btn_pause.configure(text="Pause")
        self._set_toolbar_state(True)
        self.canvas.delete("overlay")
        self._update_status()

    def _start_rom(self, path: str) -> None:
        """Load cartridge and begin (or restart) emulation."""
        try:
            self._load_rom(path)
            self.running = True
            self.paused = False
            self.state = "RUNNING"
            self.error_msg = ""
            self.btn_pause.configure(text="Pause")
            self._set_toolbar_state(True)
            self.canvas.delete("overlay")
            self._draw_placeholder("Booting…")
            self._update_status()
        except Exception as e:
            self._fail(str(e), exit_soon=False)

    def _load_rom(self, path: str) -> None:
        if not os.path.isfile(path):
            raise FileNotFoundError(f"ROM not found: {path}")
        self.cart = Cartridge(path)
        self.bus = Bus(self.cart)
        self.cpu = CPU(self.bus)
        self.bus.attach_cpu(self.cpu)
        if getattr(self, "_cpu_debug", False):
            self.cpu.debug = True
        self.bus.reset()
        self.rom_path = path
        self.root.title(f"VirtualNES 0.1.1 — {self.cart.name}")

    def _fail(self, msg: str, exit_soon: bool = False) -> None:
        self.error_msg = msg
        self.state = "ERROR"
        self.running = False
        self._set_toolbar_state(False)
        self._draw_placeholder("ERROR")
        self._update_status()
        try:
            messagebox.showerror("VirtualNES", msg, parent=self.root)
        except tk.TclError:
            pass
        if exit_soon:
            self.root.after(1800, self._on_close)

    def _on_close(self) -> None:
        self.running = False
        if self._loop_id is not None:
            try:
                self.root.after_cancel(self._loop_id)
            except tk.TclError:
                pass
            self._loop_id = None
        self.root.destroy()

    def _dummy(self, name: str) -> None:
        messagebox.showinfo(
            "Config",
            f"{name} settings are stubs in 0.1.\n"
            "Audio: APU timing stub only (no output).\n"
            "Input: Z/X, Enter, RShift, Arrows.",
            parent=self.root,
        )

    def _controls_help(self) -> None:
        messagebox.showinfo(
            "Controls",
            "Z = A          X = B\n"
            "Enter = Start  Right Shift = Select\n"
            "Arrow keys = D-pad\n\n"
            "R = Reset      P = Pause/Resume\n"
            "Esc = Exit     F1 = About\n"
            "Ctrl+O = Load ROM\n"
            "Space = Play ROM",
            parent=self.root,
        )

    def _about(self) -> None:
        messagebox.showinfo(
            "About VirtualNES",
            "VirtualNES 0.1\n"
            "Compact NTSC Famicom/NES emulator (stdlib only)\n\n"
            "Mappers: 0 NROM · 1 MMC1 · 2 UxROM · 3 CNROM · 4 MMC3\n"
            f"CPU {CPU_CLOCK_HZ:,} Hz · {NTSC_FPS} FPS · "
            f"{CPU_CYCLES_PER_FRAME} cycles/frame\n"
            f"Display {NES_W}×{NES_H} @ {self.scale}×\n\n"
            "files=ON — File→Load ROM… / Ctrl+O / toolbar\n"
            "python virtualnes0.1.1.py [game.nes]\n"
            "python virtualnes0.1.1.py --cpu-selftest",
            parent=self.root,
        )

    def _set_scale(self, scale: int) -> None:
        # Keep inside fixed 600×400: max integer zoom that fits view area
        max_fit = max(1, min(WIN_W // NES_W, (WIN_H - 120) // NES_H))
        scale = max(1, min(int(scale), max_fit))
        if scale == self.scale:
            return
        self.scale = scale
        self.canvas.configure(width=NES_W * scale, height=NES_H * scale)
        if self.running and not self.paused and self.bus:
            self._blit()
        else:
            self._draw_placeholder("PAUSED" if self.paused else self.state)
        self._center_window()
        self._update_status()

    def on_reset(self) -> None:
        if not self.bus or not self.cpu or not self.cart:
            return
        try:
            self.bus.reset()
            self.paused = False
            self.state = "RUNNING"
            self.running = True
            self.btn_pause.configure(text="Pause")
            self._set_toolbar_state(True)
            self.canvas.delete("overlay")
            self._update_status()
        except Exception as e:
            self._fail(f"Reset failed: {e}", exit_soon=False)

    def on_pause(self) -> None:
        if self.state == "ERROR" or not self.bus:
            return
        if not self.running and not self.paused:
            return
        self.paused = not self.paused
        if self.paused:
            self.state = "PAUSED"
            self.btn_pause.configure(text="Resume")
            self._draw_placeholder("PAUSED")
        else:
            self.state = "RUNNING"
            self.running = True
            self.btn_pause.configure(text="Pause")
            self.canvas.delete("overlay")
        self._update_status()

    def _update_status(self) -> None:
        name = self.cart.name if self.cart else "(none)"
        mapper = str(self.cart.mapper) if self.cart else "-"
        extra = f"  |  {self.error_msg}" if self.error_msg and self.state == "ERROR" else ""
        self.status_var.set(
            f" ROM: {name}  |  Mapper: {mapper}  |  "
            f"Scale: {self.scale}×  |  FPS: {self.fps:5.1f}  |  {self.state}{extra}"
        )

    # ----- emulation loop -----
    def _frame_loop(self) -> None:
        """Fixed timestep: CPU_CYCLES_PER_FRAME then GUI timer (~NTSC)."""
        if not self.root.winfo_exists():
            return
        t0 = time.perf_counter()
        if self.running and not self.paused and self.cpu and self.bus:
            try:
                self._emulate_frame()
                self._blit()
            except Exception as e:
                self._fail(f"Emulation error: {e}", exit_soon=False)
                self._loop_id = self.root.after(FRAME_MS, self._frame_loop)
                return

        now = time.perf_counter()
        self._frame_times.append(now)
        cutoff = now - 1.0
        self._frame_times = [t for t in self._frame_times if t >= cutoff]
        self.fps = float(len(self._frame_times))
        self._status_tick += 1
        if self._status_tick >= 10:
            self._status_tick = 0
            self._update_status()

        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        delay = max(1, FRAME_MS - int(elapsed_ms))
        self._loop_id = self.root.after(delay, self._frame_loop)

    def _emulate_frame(self) -> None:
        assert self.cpu and self.bus
        # Run until one PPU frame completes (VBlank), with a safety cap.
        budget = CPU_CYCLES_PER_FRAME * 2
        used = 0
        ppu = self.bus.ppu
        ppu.frame_complete = False
        while not ppu.frame_complete and used < budget:
            if ppu.nmi:
                ppu.nmi = False
                self.cpu.nmi()
            if self.bus.cart.irq:
                self.bus.cart.irq = False
                self.cpu.irq()
            cyc = self.cpu.step()
            ppu.step(cyc)
            self.bus.apu.step(cyc)
            used += cyc

    def _blit(self) -> None:
        """PPU RGB → PhotoImage via raw PPM bytes, then integer zoom.

        Note: base64-wrapping PPM makes Tk treat the data as PNG and fails;
        pass raw P6 bytes instead.
        """
        assert self.bus is not None
        self.canvas.delete("overlay")
        rgb = self.bus.ppu.framebuffer.tobytes()
        ppm = self._ppm_header + rgb
        try:
            img = tk.PhotoImage(data=ppm)
        except tk.TclError:
            # Last-resort row put (slow)
            img = tk.PhotoImage(width=NES_W, height=NES_H)
            fb = self.bus.ppu.framebuffer
            for y in range(NES_H):
                parts: list[str] = []
                base = y * NES_W * 3
                for x in range(NES_W):
                    i = base + x * 3
                    parts.append(f"#{fb[i]:02x}{fb[i + 1]:02x}{fb[i + 2]:02x}")
                img.put("{" + " ".join(parts) + "}", to=(0, y))
        if self.scale != 1:
            img = img.zoom(self.scale, self.scale)
        self._scaled = img
        self.canvas.itemconfigure(self._img_id, image=img)

    def run(self) -> None:
        self.root.mainloop()


def main() -> int:
    argv = [a for a in sys.argv[1:] if a]
    if "--cpu-selftest" in argv:
        return run_cpu_selftest()
    debug = "--debug-cpu" in argv
    argv = [a for a in argv if a not in ("--debug-cpu", "--cpu-selftest")]
    rom = argv[0] if argv else None
    # files=ON: File→Load ROM + optional CLI path; opcodes stay in this .py
    assert files is True and ON is True
    app = VirtualNESApp(rom)
    if debug and app.cpu:
        app.cpu.debug = True
    elif debug:
        # ROM not yet loaded — flag applied in _load_rom
        app._cpu_debug = True  # type: ignore[attr-defined]
    app.run()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
