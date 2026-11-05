#!/usr/bin/env python3
"""
Ranch RNG Tool - RNG manipulation helper for the Mew / Phione that Hayley trades in
My Pokémon Ranch / Minna no Pokémon Bokujō (WiiWare).

The trade generator reads three consecutive rand() calls from the IV seed (the rand() "next" word
at the generator entry) and builds the IV word from them, as in ranch_mew_phione.py:

    a, b, c = first, second and third rand() output (15 bits each)
    IV word = c + (a << 15) + (b << 30)
    PS = bits 0-4, Atk = 5-9, Def = 10-14, Spd = 15-19, SpAtk = 20-24, SpDef = 25-29

so PS/Atk/Def come from the third call and Spd/SpAtk/SpDef from the first one.

Generator tab: spreads of the IV seed advanced Min Advances..Max Advances times (one advance = one
rand() call), filtered by IV ranges.
Searcher tab: every IV seed whose spread fits the IV ranges, found by reverse calculation. A seed
found here is the Generator's "Current Seed" at the advance that produces the spread.
In both tabs a click on an IV name sets its range to 0-31, a Ctrl+click to 31-31, and a right-click
in the IVs box copies or pastes all the ranges (as 0/0/0/0/0/0-31/31/31/31/31/31), clears them or
sets them all to 31.
Every typed field corrects itself while the user types or pastes, has Undo / Redo (Ctrl+Z / Ctrl+Y)
and a right-click menu with Undo, Redo, Cut, Copy, Paste, Delete and Select All.
Seed to RTC tab: date/time (RTC) to set so that the boot seed reaches a target seed within a range
of advances, on the emulator only. In Dolphin the boot seed is Origin Seed + 0x39EF8B0 * seconds
since 01/01/2000 00:00:00; the Origin Seed is kept in an .ini file with this script's name, next to
it (ranch_rng_tool.ini).
Trade Offset (Generator and Seed to RTC): when Phione and Mew are offered in the same deposit,
Hayley offers Phione first, and Mew's IVs are generated a number of rand() calls after the A press
that accepts that trade (Accepted) or refuses it (Refused): 62 / 23 with GER, 6 * N + 44 /
6 * N + 16 with JPN Pt, N being the number of Pokémon on the ranch (Ranch Pokémon). With the option
on, the Generator lists the seed and advance of the A press next to the IVs generated that many
calls later, and Seed to RTC aims the A press that many calls before the Target Seed.
Seed from Camera tab: the current rand() state from a sequence of camera movements of the idle
ranch (3 calls per camera), after an Initial Seed or by bruteforce over all the states.
Seed from Dex tab: the current rand() state from the Pokédex descriptions that the trade shows at
every Yes -> No -> No loop (JPN Platinum or German EUR, 1 call per description), after an Initial
Seed.
Seed from Dice tab: the current rand() state from the faces of dice rolls (JPN Platinum only, 3
calls per roll or 5 after a 1, 5 or 6), after an Initial Seed or by bruteforce over all the states.

Only the Python standard library is needed (tkinter), Python 3.8 or later. It runs on Windows,
macOS and Linux; on Linux tkinter may come as a separate package (python3-tk on Debian/Ubuntu,
python3-tkinter on Fedora), and with Homebrew on macOS as python-tk. On macOS the Ctrl+click on an
IV name is Command+click, Ctrl+A/Ctrl+C are also Command+A/Command+C, and the right-click menus also
open with Control+click.
"""
import base64
import bisect
import calendar
import configparser
import heapq
import math
import os
import re
import string
import struct
import sys
import threading
import tkinter as tk
import tkinter.font as tkfont
import webbrowser
import zlib
from array import array
from dataclasses import dataclass
from datetime import datetime, timedelta
from tkinter import ttk

APP_TITLE = "Ranch RNG Tool"
APP_DESCRIPTION = "Useful tool for RNG manipulation on My Pokémon Ranch games."
AUTHOR_NAME = "Real96"
GITHUB_URL = "https://github.com/Real96/RanchRNGTool"
THEMES = ("Light", "Dark")
DEFAULT_THEME = "Dark"
DEFAULT_WINDOW_HEIGHT = 640     # the width comes from the content (also the minimum width)
MIN_WINDOW_HEIGHT = 420

# ------------------------------------------------------------------------------------------------
# RNG core
# ------------------------------------------------------------------------------------------------

MSL_MUL = 0x41C64E6D        # Metrowerks Standard Library rand(): next = next * MUL + ADD
MSL_ADD = 12345
MASK32 = 0xFFFFFFFF
MSL_MUL_INVERSE = pow(MSL_MUL, -1, 1 << 32)

STAT_NAMES = ("PS", "Atk", "Def", "SpAtk", "SpDef", "Spd")
STAT_SHIFTS = (0, 5, 10, 20, 25, 15)    # bit offset of each STAT_NAMES entry in the IV word

DEFAULT_MAX_ADVANCES = 1_000_000
MAX_RESULTS = 5_000_000     # safety cap, every result row is kept in memory

# Trade Offset: rand() calls from the A press on Phione's offer to the generation of Mew's IVs, when
# both trades are offered in the same deposit. GER: measured in the game, with only the favourite
# Pokémon shown (EUR; USA and JPN run the same code). JPN Pt rebuilds the ranch after the offer:
# every Pokémon on it is shuffled and placed again, about 6 calls each, so N Pokémon add 6 * N.
TRADE_OFFSET_CHOICES = ("Accepted", "Refused")
TRADE_OFFSET_VERSIONS = ("JPN Pt", "GER")       # the names of the Seed from Dex versions
DEFAULT_TRADE_OFFSET_VERSION = "JPN Pt"
DEFAULT_RANCH_POKEMON = 40
TRADE_OFFSETS = {"GER": {"Accepted": 62, "Refused": 23},
                 "JPN Pt": {"Accepted": 44, "Refused": 16}}
CALLS_PER_RANCH_POKEMON = {"GER": 0, "JPN Pt": 6}
MAX_RANCH_POKEMON = 1500        # JPN Pt places at most 1,500 Pokémon (the limit in its code)
SEARCH_CHUNK = 1 << 16      # advances between two cancel/progress checks

U32 = "I" if array("I").itemsize == 4 else "L"     # array typecode for unsigned 32-bit values


def _rand_jumps():
    """(multiplier, increment) that advance the rand() state by 2^i calls, for i = 0..31."""
    jumps = []
    mul, add = MSL_MUL, MSL_ADD
    for _ in range(32):
        jumps.append((mul, add))
        mul, add = (mul * mul) & MASK32, (add * mul + add) & MASK32
    return tuple(jumps)


RAND_JUMPS = _rand_jumps()


def rand_previous(state):
    """rand() state before one call."""
    return ((state - MSL_ADD) * MSL_MUL_INVERSE) & MASK32


def rand_distance(start, end):
    """Number of rand() calls (0 .. 2^32 - 1) that take the state `start` to `end`.

    The low k bits of the state repeat every 2^k calls, so jumping 2^i calls keeps the bits
    below i and flips bit i: matching the bits from the lowest up gives the distance.
    """
    distance = 0
    bit = 1
    for mul, add in RAND_JUMPS:
        if (start ^ end) & bit:
            start = (start * mul + add) & MASK32
            distance |= bit
        bit <<= 1
    return distance


def rand_jump(steps):
    """(multiplier, increment) that advance the rand() state by `steps` calls (mod 2^32).

    The cycle is 2^32 long, so steps = 2^32 - n goes n calls back.
    """
    mul, add = 1, 0
    for bit, (jump_mul, jump_add) in enumerate(RAND_JUMPS):
        if steps >> bit & 1:
            mul, add = (jump_mul * mul) & MASK32, (jump_mul * add + jump_add) & MASK32
    return mul, add


def rand_advance(state, steps):
    """rand() state after `steps` calls (negative values go back)."""
    mul, add = rand_jump(steps & MASK32)
    return (state * mul + add) & MASK32


def advance_states(states, steps):
    """Copy of the array `states` with every rand() state advanced by `steps` calls (negative
    values go back)."""
    mul, add = rand_jump(steps & MASK32)
    return array(U32, ((state * mul + add) & MASK32 for state in states))


def trade_offset(choice, version, ranch_pokemon=0):
    """rand() calls from the A press that accepts or refuses Phione's trade (`choice`, a
    TRADE_OFFSET_CHOICES entry) to the generation of Mew's IVs, in `version` (a
    TRADE_OFFSET_VERSIONS entry) with `ranch_pokemon` Pokémon on the ranch."""
    return TRADE_OFFSETS[version][choice] + CALLS_PER_RANCH_POKEMON[version] * ranch_pokemon


class SearchProgress:
    """Search state written by the worker thread and read by the UI thread."""

    def __init__(self):
        self.done = 0
        self.total = 0
        self.phase = "Searching..."


def estimate_seed_count(iv_ranges):
    """Average number of IV seeds whose spread fits iv_ranges (4 per spread)."""
    count = 4
    for low, high in iv_ranges:
        count *= high - low + 1
    return count


def _stat_triple_table(range0, range1, range2):
    """Filter table indexed by the top 16 bits of a rand() state.

    rand() returns bits 16-30 of the state, and the IV word stores that 15-bit value as three
    5-bit stats. Entry v is 1 when the stats in bits 0-4, 5-9 and 10-14 of v are within their
    (min, max) ranges.
    """
    ok0, ok1, ok2 = (bytes(low <= iv <= high for iv in range(32))
                     for low, high in (range0, range1, range2))
    return bytes(ok0[v & 31] & ok1[(v >> 5) & 31] & ok2[(v >> 10) & 31] for v in range(1 << 16))


def _value_runs(table):
    """Runs (start, length) of consecutive 15-bit values accepted by a _stat_triple_table."""
    accepted = table[:1 << 15]
    runs = []
    start = accepted.find(1)
    while start >= 0:
        end = accepted.find(0, start)
        if end < 0:
            end = len(accepted)
        runs.append((start, end - start))
        start = accepted.find(1, end)
    return runs


# ------------------------------------------------------------------------------------------------
# Reverse calculation: from IV ranges to seeds
# ------------------------------------------------------------------------------------------------
#
# From the seed s0 the generator reads s1 = f(s0), s2 = f(s1), s3 = f(s2). Spd/SpAtk/SpDef are bits
# 16-30 of s1, PS/Atk/Def bits 16-30 of s3, and s3 = M2 * s1 + C2 with M2/C2 the constants of two
# calls. Bit 31 never reaches the IVs, so modulo 2^31 the pairs (s1, s3 - C2) are exactly the
# points of the lattice {(x, y) : y = M2 * x (mod 2^31)}.
#
# A run of consecutive accepted values of the first call fixes an interval of s1, a run of the
# third call an interval of s3: together a box in that plane. With a lattice basis reduced for
# the shape of the box (Lagrange reduction) the points inside it are listed line by line with a
# few operations each, about two points per spread. Every point gives two seeds, since bit 31 of
# s1 is free. It is the idea behind PokeFinder's LCRNGReverse, whose constants are a reduced
# basis for one spread and the PokeRNG increment; here the basis is computed for this rand()
# and for whole IV ranges at once.

TWO_CALLS_MUL = (MSL_MUL * MSL_MUL) & MASK32
TWO_CALLS_ADD = (MSL_ADD * MSL_MUL + MSL_ADD) & MASK32
LATTICE_MOD = 1 << 31
LATTICE_MUL = TWO_CALLS_MUL % LATTICE_MOD
LATTICE_ADD = TWO_CALLS_ADD % LATTICE_MOD
_UNBOUNDED = 1 << 62


def _reduced_basis(weight_x, weight_y):
    """Reduced basis (u, v, det) of the lattice for the norm (x*weight_x)^2 + (y*weight_y)^2.

    u is the shortest vector and det = det(v, u) = 2^31 (u is flipped to make it positive).
    """
    wx2, wy2 = weight_x * weight_x, weight_y * weight_y

    def dot(p, q):
        return p[0] * q[0] * wx2 + p[1] * q[1] * wy2

    u, v = (1, LATTICE_MUL), (0, LATTICE_MOD)
    if dot(u, u) > dot(v, v):
        u, v = v, u
    while True:
        norm_u = dot(u, u)
        k = (2 * dot(u, v) + norm_u) // (2 * norm_u)    # nearest integer to <u,v> / <u,u>
        v = (v[0] - k * u[0], v[1] - k * u[1])
        if dot(v, v) >= norm_u:
            break
        u, v = v, u
    det = v[0] * u[1] - v[1] * u[0]
    if det < 0:
        u, det = (-u[0], -u[1]), -det
    return u, v, det


def _steps_within(base, step, low, high):
    """Inclusive range of the integers j with low <= base + j * step <= high."""
    if step > 0:
        return -((base - low) // step), (high - base) // step
    if step < 0:
        return -((high - base) // -step), (base - low) // -step
    return (-_UNBOUNDED, _UNBOUNDED) if low <= base <= high else (1, 0)


def _box_points(basis, x0, x1, y0, y1):
    """Lattice points (x, y) with x0 <= x < x1 and y0 <= y < y1."""
    (ux, uy), (vx, vy), det = basis
    x1 -= 1
    y1 -= 1
    # Every point is i*v + j*u with i = det(p, u) / det, a linear function of p, so the range of
    # i over the box comes from its corners. Each i is a line parallel to the short vector u.
    ends = (x0 * uy - y0 * ux, x0 * uy - y1 * ux, x1 * uy - y0 * ux, x1 * uy - y1 * ux)
    points = []
    for i in range(-(-min(ends) // det), max(ends) // det + 1):
        base_x, base_y = i * vx, i * vy
        j_min, j_max = _steps_within(base_x, ux, x0, x1)
        y_min, y_max = _steps_within(base_y, uy, y0, y1)
        for j in range(max(j_min, y_min), min(j_max, y_max) + 1):
            points.append((base_x + j * ux, base_y + j * uy))
    return points


class SpreadFilter:
    """IV ranges compiled for the first rand() call (Spd/SpAtk/SpDef) and the third (PS/Atk/Def)."""

    def __init__(self, iv_ranges):
        self.first_ok = _stat_triple_table(iv_ranges[5], iv_ranges[3], iv_ranges[4])
        self.third_ok = _stat_triple_table(iv_ranges[0], iv_ranges[1], iv_ranges[2])
        self.first_runs = _value_runs(self.first_ok)
        self.third_runs = _value_runs(self.third_ok)
        self.box_count = len(self.first_runs) * len(self.third_runs)
        self.seed_estimate = estimate_seed_count(iv_ranges)

    def seeds(self, cancel=None, progress=None):
        """Yield (seed, IV word) for every IV seed whose spread passes the filter, unsorted."""
        if progress is not None:
            progress.total = self.box_count
        bases = {}
        for first_start, first_length in self.first_runs:
            x0, x1 = first_start << 16, (first_start + first_length) << 16
            for third_start, third_length in self.third_runs:
                if cancel is not None and cancel.is_set():
                    return
                shape = (first_length, third_length)
                basis = bases.get(shape)
                if basis is None:
                    # Scaling x by the y extent and y by the x extent turns the box into a square.
                    basis = bases[shape] = _reduced_basis(third_length, first_length)
                y0 = (third_start << 16) - LATTICE_ADD
                y1 = ((third_start + third_length) << 16) - LATTICE_ADD
                for s1, y in _box_points(basis, x0, x1, y0, y1):
                    ivs = ((y + LATTICE_ADD) >> 16) | ((s1 >> 16) << 15)
                    seed = rand_previous(s1)
                    yield seed, ivs
                    yield seed ^ 0x80000000, ivs
                if progress is not None:
                    progress.done += 1


# ------------------------------------------------------------------------------------------------
# Searches (they run on a worker thread)
# ------------------------------------------------------------------------------------------------

@dataclass
class GeneratorOutcome:
    seeds: array        # rand() state of each hit, the "Current Seed" column: the IV seed, or with
                        # a Trade Offset the state that many calls before it
    advances: array     # advance of each hit, ascending
    ivs: array          # 30-bit IV word of each hit
    first: int          # first advance examined (Min Advances)
    scanned: int        # advances examined (first .. first + scanned - 1); None if not a prefix
    status: str         # "done", "cancelled" or "limit"


@dataclass
class SpreadOutcome:
    seeds: array        # IV seeds, ascending
    ivs: array          # 30-bit IV word of each seed
    status: str         # "done", "cancelled" or "limit"


# Rough per-item costs used to choose the Generator strategy (CPython on a desktop PC).
SCAN_SECONDS_PER_ADVANCE = 0.3e-6
SEEK_SECONDS_PER_BOX = 5e-6
SEEK_SECONDS_PER_SEED = 11e-6


def search_ivs(seed, min_advances, max_advances, iv_ranges, cancel=None, progress=None,
               max_results=MAX_RESULTS, method="auto", offset=0):
    """Spreads of the IV seed `seed` advanced min_advances..max_advances times that fit iv_ranges.

    Two equivalent strategies: "scan" generates every advance; "seek" lists every seed in the
    whole RNG cycle whose spread fits (reverse calculation) and keeps those within reach,
    measuring their distance from `seed`. "auto" picks the one expected to be faster.
    With an `offset` (the Trade Offset), the spread of each advance is generated `offset` rand()
    calls later; the seeds and advances listed stay those of the advance itself.
    """
    spread_filter = SpreadFilter(iv_ranges)
    if method == "auto":
        seek_cost = (spread_filter.box_count * SEEK_SECONDS_PER_BOX
                     + spread_filter.seed_estimate * SEEK_SECONDS_PER_SEED)
        scan_cost = (max_advances - min_advances + 1) * SCAN_SECONDS_PER_ADVANCE
        fits = spread_filter.seed_estimate <= max_results
        method = "seek" if fits and seek_cost < scan_cost else "scan"
    # Advance n of `seed` + offset calls = advance n of the seed `offset` calls further on.
    start = rand_advance(seed, offset)
    if method == "seek":
        outcome = _seek_advances(start, min_advances, max_advances, spread_filter, cancel,
                                 progress)
    else:
        outcome = _scan_advances(start, min_advances, max_advances, spread_filter, cancel,
                                 progress, max_results)
    if offset:
        outcome.seeds = advance_states(outcome.seeds, -offset)
    return outcome


def _scan_advances(seed, min_advances, max_advances, spread_filter, cancel, progress, max_results):
    first_ok, third_ok = spread_filter.first_ok, spread_filter.third_ok
    seeds, advances, ivs = array(U32), array(U32), array(U32)
    add_seed, add_advance, add_ivs = seeds.append, advances.append, ivs.append
    mul, inc, mask = MSL_MUL, MSL_ADD, MASK32

    state = rand_advance(seed, min_advances)    # rand() state at the current advance
    s1 = (state * mul + inc) & mask     # states after the generator's 1st, 2nd and 3rd call
    s2 = (s1 * mul + inc) & mask
    s3 = (s2 * mul + inc) & mask

    total = max_advances - min_advances + 1
    if progress is not None:
        progress.total = total
    scanned = 0
    status = "done"
    while scanned < total:
        if cancel is not None and cancel.is_set():
            status = "cancelled"
            break
        stop = min(scanned + SEARCH_CHUNK, total)
        for advance in range(min_advances + scanned, min_advances + stop):
            if first_ok[s1 >> 16] and third_ok[s3 >> 16]:
                add_seed(state)
                add_advance(advance)
                add_ivs(((s3 >> 16) & 0x7FFF) | (((s1 >> 16) & 0x7FFF) << 15))
            state, s1, s2, s3 = s1, s2, s3, (s3 * mul + inc) & mask
        scanned = stop
        if progress is not None:
            progress.done = scanned
        if len(seeds) > max_results or (len(seeds) == max_results and scanned < total):
            del seeds[max_results:], advances[max_results:], ivs[max_results:]
            scanned = advances[-1] - min_advances + 1
            status = "limit"
            break
    return GeneratorOutcome(seeds, advances, ivs, min_advances, scanned, status)


def _seek_advances(seed, min_advances, max_advances, spread_filter, cancel, progress):
    hits = []
    for state, ivs in spread_filter.seeds(cancel, progress):
        advance = rand_distance(seed, state)
        if min_advances <= advance <= max_advances:
            hits.append((advance, state, ivs))
    cancelled = cancel is not None and cancel.is_set()
    hits.sort()
    advances, states, words = (array(U32, (hit[index] for hit in hits)) for index in range(3))
    return GeneratorOutcome(states, advances, words, min_advances,
                            None if cancelled else max_advances - min_advances + 1,
                            "cancelled" if cancelled else "done")


def search_spreads(iv_ranges, cancel=None, progress=None, max_results=MAX_RESULTS):
    """Every IV seed whose spread fits iv_ranges, sorted by seed."""
    seeds, ivs = array(U32), array(U32)
    add_seed, add_ivs = seeds.append, ivs.append
    status = "done"
    for seed, spread in SpreadFilter(iv_ranges).seeds(cancel, progress):
        add_seed(seed)
        add_ivs(spread)
        if len(seeds) > max_results:
            del seeds[max_results:], ivs[max_results:]
            status = "limit"
            break
    if status == "done" and cancel is not None and cancel.is_set():
        status = "cancelled"
    if progress is not None:
        progress.phase = "Sorting..."
    order = sorted(range(len(seeds)), key=seeds.__getitem__)
    return SpreadOutcome(array(U32, map(seeds.__getitem__, order)),
                         array(U32, map(ivs.__getitem__, order)), status)


# ------------------------------------------------------------------------------------------------
# Seed to RTC: date/time whose boot seed reaches a target seed
# ------------------------------------------------------------------------------------------------
#
# Dolphin derives the boot seed from the RTC: seed(t) = Origin + 0x39EF8B0 * t (mod 2^32), with t
# the seconds since 01/01/2000 00:00:00 and 0x39EF8B0 = 60,750,000 the Wii Time Base frequency.
# 0x39EF8B0 = 16 * 3,796,875 (odd), so every boot seed keeps the low 4 bits of the Origin Seed and
# the same seed comes back every 2^28 seconds (about 8.5 years).

RTC_EPOCH = datetime(2000, 1, 1)
RTC_LAST_SECOND = int((datetime(2036, 12, 31, 23, 59, 59) - RTC_EPOCH).total_seconds())
RTC_TICKS_PER_SECOND = 0x39EF8B0
RTC_SEED_PERIOD = 1 << 28
RTC_TICKS_INVERSE = pow(RTC_TICKS_PER_SECOND >> 4, -1, RTC_SEED_PERIOD)
RTC_FORMAT = "%d/%m/%Y %H:%M:%S"
RTC_SCAN_CHUNK = 1 << 12        # seconds between two cancel/progress checks
RTC_SEEK_CHUNK = 1 << 13        # target predecessors between two cancel/progress checks
RAND_BACK_16 = rand_jump(-16 & MASK32)
DEFAULT_ORIGIN_SEED = 0x058511BF
DEFAULT_MIN_ADVANCES = 1_000
DEFAULT_RTC_MAX_RESULTS = 10

# Rough per-item costs used to choose the Seed to RTC strategy (CPython on a desktop PC).
RTC_SCAN_SECONDS_PER_SECOND = 7e-6
RTC_SEEK_SECONDS_PER_STATE = 0.45e-6
RTC_SEEK_SECONDS_PER_HIT = 1e-6


def rtc_text(seconds):
    """dd/mm/yyyy hh:mm:ss of the RTC `seconds` after 01/01/2000 00:00:00."""
    return (RTC_EPOCH + timedelta(seconds=seconds)).strftime(RTC_FORMAT)


def boot_seed(origin, seconds):
    """IV seed computed at boot for the RTC `seconds` after 01/01/2000 00:00:00."""
    return (origin + RTC_TICKS_PER_SECOND * seconds) & MASK32


@dataclass
class RtcOutcome:
    seconds: array      # RTC of each result (seconds since 01/01/2000 00:00:00), ascending
    seeds: array        # boot seed (Initial Seed) of each result
    advances: array     # rand() calls from the boot seed to the target seed
    status: str         # "done", "limit" (Max Results reached) or "cancelled"


def search_rtc(origin, target, first_second, min_advances, max_advances, max_results,
               cancel=None, progress=None, method="auto", offset=0):
    """The first `max_results` RTCs from `first_second` on whose boot seed reaches `target` after
    min_advances..max_advances rand() calls.

    "scan" checks one second after the other; "seek" walks back from the target over the allowed
    advances and solves Origin + 0x39EF8B0 * t = state for t. Same results; "auto" picks the one
    expected to be faster.
    With an `offset` (the Trade Offset), the advances lead to the state `offset` calls before
    `target`, which then comes `offset` calls after them.
    """
    target = rand_advance(target, -offset)
    # All boot seeds share the low 4 bits of the Origin Seed, so all their distances to the
    # target have the same residue mod 16: the first advance with that residue may be the minimum.
    residue = rand_distance(origin, target) & 15
    first_advance = min_advances + ((residue - min_advances) & 15)
    if first_advance > max_advances or first_second > RTC_LAST_SECOND:
        return RtcOutcome(array(U32), array(U32), array(U32), "done")
    if method == "auto":
        span = RTC_LAST_SECOND - first_second + 1
        window = max_advances - min_advances + 1
        hits = span * window / 2**32        # expected results in the whole date range
        scanned = span if hits <= max_results else span * max_results / hits
        scan_cost = scanned * RTC_SCAN_SECONDS_PER_SECOND
        seek_cost = window / 16 * RTC_SEEK_SECONDS_PER_STATE + hits * RTC_SEEK_SECONDS_PER_HIT
        method = "seek" if seek_cost < scan_cost else "scan"
    if method == "seek":
        return _rtc_seek(origin, target, first_second, first_advance, max_advances, max_results,
                         cancel, progress)
    return _rtc_scan(origin, target, first_second, min_advances, max_advances, max_results,
                     cancel, progress)


def _rtc_scan(origin, target, first_second, min_advances, max_advances, max_results, cancel,
              progress):
    seconds, seeds, advances = array(U32), array(U32), array(U32)
    span = RTC_LAST_SECOND - first_second + 1
    if progress is not None:
        progress.total = 1000
    seed = boot_seed(origin, first_second)
    second = first_second
    status = "done"
    while second <= RTC_LAST_SECOND and status == "done":
        if cancel is not None and cancel.is_set():
            status = "cancelled"
            break
        stop = min(second + RTC_SCAN_CHUNK, RTC_LAST_SECOND + 1)
        for moment in range(second, stop):
            advance = rand_distance(seed, target)
            if min_advances <= advance <= max_advances:
                seconds.append(moment)
                seeds.append(seed)
                advances.append(advance)
                if len(seconds) == max_results:
                    status = "limit"
                    break
            seed = (seed + RTC_TICKS_PER_SECOND) & MASK32
        second = stop
        if progress is not None:        # the share of the dates or of the results, if larger
            progress.done = int(1000 * max(len(seconds) / max_results,
                                           (second - first_second) / span))
    return RtcOutcome(seconds, seeds, advances, status)


def _rtc_seek(origin, target, first_second, first_advance, max_advances, max_results, cancel,
              progress):
    state = rand_advance(target, -first_advance)    # reaches the target in first_advance calls
    back_mul, back_add = RAND_BACK_16
    count = (max_advances - first_advance) // 16 + 1
    if progress is not None:
        progress.total = count
    earliest = []       # heap of (-second, seed, advance): the max_results earliest RTCs so far
    advance = first_advance
    done = 0
    while done < count:
        if cancel is not None and cancel.is_set():
            break
        stop = min(done + RTC_SEEK_CHUNK, count)
        for _ in range(done, stop):
            # Origin + 16 * k * t = state (mod 2^32)  =>  t = ((state - Origin) / 16) / k (mod 2^28)
            second = ((((state - origin) & MASK32) >> 4) * RTC_TICKS_INVERSE) % RTC_SEED_PERIOD
            if second < first_second:
                second += -((second - first_second) // RTC_SEED_PERIOD) * RTC_SEED_PERIOD
            while second <= RTC_LAST_SECOND:
                if len(earliest) < max_results:
                    heapq.heappush(earliest, (-second, state, advance))
                elif second < -earliest[0][0]:
                    heapq.heapreplace(earliest, (-second, state, advance))
                else:
                    break           # the next occurrences of this seed are even later
                second += RTC_SEED_PERIOD
            state = (state * back_mul + back_add) & MASK32
            advance += 16
        done = stop
        if progress is not None:
            progress.done = done
    cancelled = cancel is not None and cancel.is_set()
    earliest.sort(reverse=True)     # ascending RTC
    status = "cancelled" if cancelled else "limit" if len(earliest) == max_results else "done"
    return RtcOutcome(array(U32, (-item[0] for item in earliest)),
                      array(U32, (item[1] for item in earliest)),
                      array(U32, (item[2] for item in earliest)), status)


# ------------------------------------------------------------------------------------------------
# Seed from Camera, Seed from Dex and Seed from Dice: the rand() state from what the game shows
# ------------------------------------------------------------------------------------------------
#
# Camera (same code and same camera data in every build): in free mode a per-frame update (EUR
# 0x802E958C, USA 0x802E6A94, JPN 0x802D6420, JPN Platinum 0x80367D04) starts a new shot when the
# previous one has ended. The shots are "autocamera__0" to "autocamera__9" (acm.arc/camera.brres,
# SCN0 animations of about 5 seconds that do not loop). The shot is drawn with RandRange(0, 9) =
# rand() % 10 and the camera angle around its target with RandFloat(0, 2 pi): 3 calls per camera.
# The ten shots make seven movements (CAMERA_OF_SHOT, the table of RanchRNGtool v1.0). The code
# would show the next shot when the drawn one equals the one still playing, but it reads the
# playing shot only while it plays, and this update draws only after it ended: the same shot can
# follow itself and nothing changes the 3 calls. (A missing camera target costs extra calls to
# pick one at random: the guide's focus lock avoids it.)
#
# Pokédex: the profile of the Pokémon offered in a trade picks its description with one call, so
# every Yes -> No -> No loop takes one call (none for an Egg). JPN Platinum (0x8011EA74) draws
# RandRange(0, 2) = rand() % 3: 0 Diamond, 1 Pearl, 2 Platinum, and Leafeon's Diamond and Pearl
# texts are the same. The other builds (EUR 0x800F8AF4, USA 0x800F7AB8, JPN 0x800EDEF0) draw
# RandRange(0, 1) = rand() % 2: 0 Diamond, 1 Pearl. Leafeon's two texts are the same in every
# language but German, where Diamond reads "Genau wie ein Pflanze" and Pearl "Genau wie eine
# Pflanze". rand() % 2 is bit 16 of the state, so the German descriptions repeat every 2^17 calls.
#
# Dice: only JPN Platinum has the dice toy ("さいころ", from the toy box). A roll is the state
# machine of XA::saikoro_asobi (0x801B0050). When the thrown dice lands, a landing effect
# (0x800D58DC) draws a RandFloat (2 calls), then the face is RandRange(1, 6) = rand() % 6 + 1, and
# the faces 1, 5 and 6 start one more effect (0x800E7388) with a RandFloat. So a roll the player
# throws takes 3 calls, or 5 when it shows 1, 5 or 6, as the guide's author measured, and its face
# is its third call. (A dice that a Pokémon throws also draws the throw first: RandRange(6, 12) and
# a RandFloat.)

CAMERA_MOVES = ("Zoom In", "Zoom Out", "Up-Down", "Left-Right", "Right-Left", "Up + Up-Down",
                "Up + Zoom In")         # v1.0: 拡大 縮小 上下 左右 右左 上+上下 上+拡大
NOT_CLEAR = "Not Clear"                 # v1.0: 不明, accepts any movement
NOT_CLEAR_CODE = -1
CAMERA_OF_SHOT = (0, 0, 4, 0, 5, 3, 6, 2, 1, 2)     # autocamera__N -> index in CAMERA_MOVES
SHOT_COUNT = 10
ALL_SHOTS = (1 << SHOT_COUNT) - 1      # bit masks of shots: bit N = autocamera__N
MOVE_SHOTS = tuple(sum(1 << shot for shot in range(SHOT_COUNT) if CAMERA_OF_SHOT[shot] == move)
                   for move in range(len(CAMERA_MOVES)))
CALLS_PER_CAMERA = 3
CAMERA_PREDICTIONS = 3                  # next movements shown with every result
BRUTEFORCE_MIN_CAMERAS = 13             # known movements (not Not Clear) a bruteforce needs
# Symbol tables of the scans: state >> 16 -> the value drawn by the call that leads to that state.
SHOT_SYMBOLS = bytes(48 + (value & 0x7FFF) % 10 for value in range(1 << 16))      # "0".."9"

DICE_FACES = (1, 2, 3, 4, 5, 6)
DICE_FACE_CALL = 3                      # the face is the third call of a roll
DICE_EFFECT_FACES = (1, 5, 6)           # faces whose effect takes two more calls
DICE_PREDICTIONS = 5                    # next faces shown with every result
BRUTEFORCE_MIN_ROLLS = 13               # rolls a bruteforce needs: 6^13 > 2^32
DICE_SYMBOLS = bytes(49 + (value & 0x7FFF) % 6 for value in range(1 << 16))       # "1".."6"


def roll_calls(face):
    """rand() calls a dice roll showing `face` takes."""
    return 5 if face in DICE_EFFECT_FACES else 3


class DexVersion:
    """How a build picks Leafeon's Pokédex description, and how the Seed from Dex tab shows the two
    descriptions that can be told apart (index 0 and 1)."""

    def __init__(self, name, modulus, description_of_draw, short_names, list_names, buttons):
        self.name = name                    # radio button text
        self.modulus = modulus              # the draw: RandRange(0, modulus - 1) = rand() % modulus
        self.short_names = short_names      # name in Next Descriptions
        self.list_names = list_names        # name in the entry list
        self.buttons = buttons              # button text
        # state >> 16 -> b"0" or b"1": the description shown by the call that leads to that state
        self.symbols = bytes(48 + description_of_draw[(value & 0x7FFF) % modulus]
                             for value in range(1 << 16))


DEX_VERSIONS = {version.name: version for version in (
    DexVersion("JPN Pt", 3, (0, 0, 1), ("D/P", "Pt"), ("Diamond/Pearl", "Platinum"),
               ("Diamond/Pearl\nしょくぶつ…", "Platinum\nきほんてき…")),
    DexVersion("GER", 2, (0, 1), ("D", "P"), ("Diamond", "Pearl"),
               ("Diamond\n…ein Pflanze…", "Pearl\n…eine Pflanze…")),
)}
DEFAULT_DEX_VERSION = "JPN Pt"
DEX_PREDICTIONS = 5
DEFAULT_DEX_MAX_ADVANCES = 10_000

OBSERVATION_MAX_RESULTS = 100_000
OBSERVATION_CHUNK = 1 << 18             # advances between two cancel/progress checks
LOW_MASK = (1 << 17) - 1                # bits 0-16 of a state
HIGH_MASK = (1 << 14) - 1               # bits 17-30 of a state, once shifted down

# Rough per-item costs used to choose the Seed from Camera and Seed from Dice strategy (CPython on
# a desktop PC).
OBSERVATION_SCAN_SECONDS_PER_ADVANCE = 0.25e-6
BRUTEFORCE_SECONDS_PER_LOW = 0.75e-3
SEEK_CHECK_SECONDS = 2.0                # longer scans compare their cost with a bruteforce


def predicted_cameras(state, count=CAMERA_PREDICTIONS):
    """Movements of the next `count` cameras after the rand() state `state`, e.g.
    'Zoom In → Up-Down → Zoom Out'."""
    names = []
    for _ in range(count):
        state = (state * MSL_MUL + MSL_ADD) & MASK32
        names.append(CAMERA_MOVES[CAMERA_OF_SHOT[((state >> 16) & 0x7FFF) % SHOT_COUNT]])
        state = (state * TWO_CALLS_MUL + TWO_CALLS_ADD) & MASK32     # the angle (RandFloat)
    return " → ".join(names)


def predicted_rolls(state, count=DICE_PREDICTIONS):
    """Faces of the next `count` dice rolls after the rand() state `state`, e.g. '4 → 1 → 6'."""
    faces = []
    for _ in range(count):
        state = (state * TWO_CALLS_MUL + TWO_CALLS_ADD) & MASK32     # the landing effect
        state = (state * MSL_MUL + MSL_ADD) & MASK32
        face = 1 + ((state >> 16) & 0x7FFF) % 6
        faces.append(str(face))
        if face in DICE_EFFECT_FACES:
            state = (state * TWO_CALLS_MUL + TWO_CALLS_ADD) & MASK32  # the effect of the face
    return " → ".join(faces)


def predicted_descriptions(state, version=DEFAULT_DEX_VERSION, count=DEX_PREDICTIONS):
    """The next `count` Pokédex descriptions of the build `version` (a DEX_VERSIONS key) after the
    rand() state `state`, e.g. 'D/P → Pt'."""
    dex = DEX_VERSIONS[version]
    texts = []
    for _ in range(count):
        state = (state * MSL_MUL + MSL_ADD) & MASK32
        texts.append(dex.short_names[dex.symbols[state >> 16] - 48])
    return " → ".join(texts)


@dataclass
class ObservationOutcome:
    seeds: array        # current seed of each result: the rand() state after the entries
    advances: array     # advances from the Initial Seed to the current seed; None for a bruteforce
    status: str         # "done", "cancelled" or "limit"
    method: str         # "scan", "seek" or "bruteforce"


class DrawPlan:
    """Draws of rand() % (2 * modulus) seen in a row, compiled for the searches.

    allowed[k] is the bit mask of the values draw k may show (bit v: value v), calls[k] the call
    that makes draw k, counted from the start state (1 = the first call after it), and span the
    number of calls from the start state to the current state. symbols[v] is the symbol that the
    scan's symbol table gives the value v.
    """

    def __init__(self, modulus, allowed, calls, span, symbols):
        self.modulus = modulus
        self.values = 2 * modulus
        everything = (1 << self.values) - 1
        self.allowed = list(allowed)
        self.calls = list(calls)
        self.span = span
        self.reach = self.calls[-1]                 # calls up to the last draw
        self.known = [draw for draw, mask in enumerate(self.allowed) if mask != everything]
        # One symbol per call: a class of values for each draw, any symbol for the other calls.
        parts, previous = [], 0
        for call, mask in zip(self.calls, self.allowed):
            parts.append(b"." * (call - previous - 1))
            parts.append(b"." if mask == everything else
                         b"[" + bytes(symbols[value] for value in range(self.values)
                                      if mask >> value & 1) + b"]")
            previous = call
        self.regex = re.compile(b"(?=" + b"".join(parts) + b")", re.DOTALL)
        self.draws = [rand_jump(call) for call in self.calls]
        self.to_current = rand_jump(span)
        self._lows = None

    def expected_starts(self):
        """About how many start states (bit 31 clear) a bruteforce finds."""
        count = 2.0 ** 31
        for mask in self.allowed:
            count *= bin(mask).count("1") / self.values
        return count

    def low_candidates(self):
        """Values of bits 0-16 of the start state that the parities of the draws allow.

        rand() returns bits 16-30 of the state, so the parity of a draw is bit 16 of its state,
        which depends only on bits 0-16 of the start state.
        """
        if self._lows is None:
            even_values = sum(1 << value for value in range(0, self.values, 2))
            lows = range(1 << 17)
            for (mul, add), mask in zip(self.draws, self.allowed):
                even, odd = mask & even_values, mask & ~even_values
                if even and odd:
                    continue
                mul, add, parity = mul & LOW_MASK, add & LOW_MASK, 0 if even else 1
                lows = [low for low in lows if (mul * low + add) >> 16 & 1 == parity]
            self._lows = lows
        return self._lows


class CameraPlan(DrawPlan):
    """Camera movements (CAMERA_MOVES indices, NOT_CLEAR_CODE) compiled for the searches: one shot
    rand() % 10 every 3 calls, the first at call 1."""

    def __init__(self, codes):
        # Shots each camera may have drawn: those of its movement (any for Not Clear).
        allowed = [ALL_SHOTS if code < 0 else MOVE_SHOTS[code] for code in codes]
        calls = [CALLS_PER_CAMERA * camera + 1 for camera in range(len(codes))]
        super().__init__(SHOT_COUNT // 2, allowed, calls, CALLS_PER_CAMERA * len(codes),
                         b"0123456789")


class DicePlan(DrawPlan):
    """Dice faces (1 to 6) compiled for the searches: the face rand() % 6 + 1 is the third call of
    its roll, and a roll takes 3 calls, or 5 for the faces 1, 5 and 6."""

    def __init__(self, faces):
        calls, start = [], 0
        for face in faces:
            calls.append(start + DICE_FACE_CALL)
            start += roll_calls(face)
        super().__init__(3, [1 << (face - 1) for face in faces], calls, start, b"123456")


def search_camera(seed, min_advances, max_advances, codes, bruteforce=False, cancel=None,
                  progress=None, max_results=OBSERVATION_MAX_RESULTS, method="auto"):
    """Current rand() states after cameras showing the movements `codes`.

    Without bruteforce the current state is min_advances..max_advances calls after `seed` (the
    cameras start 3 calls per camera earlier): "scan" draws every advance, "seek" runs the
    bruteforce and measures the distance of what it finds from `seed`; "auto" picks the faster.
    With bruteforce every state is a candidate and `seed` and the advances are not used.
    """
    return _search_draws(CameraPlan(codes), SHOT_SYMBOLS, seed, min_advances, max_advances,
                         bruteforce, cancel, progress, max_results, method)


def search_dice(seed, min_advances, max_advances, faces, bruteforce=False, cancel=None,
                progress=None, max_results=OBSERVATION_MAX_RESULTS, method="auto"):
    """Current rand() states after dice rolls showing `faces` (1 to 6), found like search_camera
    finds them (the rolls start 3 or 5 calls per roll earlier)."""
    return _search_draws(DicePlan(faces), DICE_SYMBOLS, seed, min_advances, max_advances,
                         bruteforce, cancel, progress, max_results, method)


def _search_draws(plan, table, seed, min_advances, max_advances, bruteforce, cancel, progress,
                  max_results, method):
    """search_camera and search_dice for a DrawPlan; table[state >> 16] is the symbol of a call."""
    if bruteforce:
        starts, cancelled = _bruteforce_starts(plan, cancel, progress)
        jump_mul, jump_add = plan.to_current
        seeds = sorted((start * jump_mul + jump_add) & MASK32 for start in starts)
        status = "cancelled" if cancelled else "done"
        if len(seeds) > max_results:
            del seeds[max_results:]
            status = "limit"
        return ObservationOutcome(array(U32, seeds), None, status, "bruteforce")
    first_frame, last_frame = max(0, min_advances - plan.span), max_advances - plan.span
    if method == "auto":
        method = "scan"
        scan_seconds = ((last_frame - first_frame + plan.reach)
                        * OBSERVATION_SCAN_SECONDS_PER_ADVANCE)
        if scan_seconds > SEEK_CHECK_SECONDS and plan.expected_starts() <= max_results:
            if len(plan.low_candidates()) * BRUTEFORCE_SECONDS_PER_LOW < scan_seconds:
                method = "seek"
    if method == "seek":
        return _seek_draws(seed, plan, min_advances, max_advances, cancel, progress, max_results)

    def find(symbols):
        return [match.start() for match in plan.regex.finditer(symbols)]

    return _scan_observations(seed, first_frame, last_frame, plan.span, plan.reach, table, find,
                              cancel, progress, max_results)


def search_dex(seed, min_advances, max_advances, codes, version=DEFAULT_DEX_VERSION, cancel=None,
               progress=None, max_results=OBSERVATION_MAX_RESULTS):
    """Current rand() states min_advances..max_advances calls after `seed` that come right after
    the Pokédex descriptions `codes` (0 or 1, see DexVersion) of the build `version`, one call
    each."""
    span = len(codes)
    pattern = bytes(48 + code for code in codes)

    def find(symbols):
        positions = []
        position = symbols.find(pattern)
        while position >= 0:
            positions.append(position)
            position = symbols.find(pattern, position + 1)
        return positions

    return _scan_observations(seed, max(0, min_advances - span), max_advances - span, span, span,
                              DEX_VERSIONS[version].symbols, find, cancel, progress, max_results)


def _scan_observations(seed, first_frame, last_frame, span, reach, table, find, cancel, progress,
                       max_results):
    """Start frames first_frame..last_frame whose next `reach` calls match, as an outcome.

    table[state >> 16] is the symbol of a call and find(symbols) lists the offsets of the windows
    that match. A result is the state `span` calls after its start frame, with its advance from
    `seed`.
    """
    seeds, advances = array(U32), array(U32)
    total = last_frame - first_frame + 1
    status = "done"
    if total <= 0:
        return ObservationOutcome(seeds, advances, status, "scan")
    if progress is not None:
        progress.total = total
    mul, inc, mask = MSL_MUL, MSL_ADD, MASK32
    base = rand_advance(seed, first_frame)      # state at `frame`, the start frame of symbols[0]
    last = base                                 # state after the last call in `symbols`
    symbols = bytearray()                       # one symbol per call: frame + 1, frame + 2, ...
    frame = first_frame
    while frame <= last_frame:
        if cancel is not None and cancel.is_set():
            status = "cancelled"
            break
        stop = min(frame + OBSERVATION_CHUNK, last_frame + 1)
        missing = stop - frame + reach - 1 - len(symbols)
        if missing > 0:
            fresh = bytearray(missing)
            state = last
            for position in range(missing):
                state = (state * mul + inc) & mask
                fresh[position] = table[state >> 16]
            last = state
            symbols += fresh
        # `symbols` ends `reach` - 1 calls after the last start frame of this round, so every
        # window found starts in this round.
        for position in find(symbols):
            seeds.append(rand_advance(base, position + span))
            advances.append(frame + position + span)
            if len(seeds) > max_results:
                status = "limit"
                del seeds[max_results:], advances[max_results:]
                break
        if status == "limit":
            break
        del symbols[:stop - frame]
        base = rand_advance(base, stop - frame)
        frame = stop
        if progress is not None:
            progress.done = frame - first_frame
    return ObservationOutcome(seeds, advances, status, "scan")


# Bruteforce. A draw of rand() % 2m is (2u + b) % 2m = 2(u % m) + b, with b = bit 16 and u = bits
# 17-30 of its state (m = 5 for the camera shots 0-9, 3 for the dice faces 1-6 minus one). Bit 16 of
# every draw depends only on bits 0-16 of the start state, so the draws whose allowed values are all
# even or all odd (every camera movement but Zoom In, every dice face) rule out most of the 2^17 low
# parts first (DrawPlan.low_candidates). With the low part fixed, u is an affine function of the 14
# high bits h (bits 17-30) of the start state, and each draw allows one or two values of u % m: the
# most selective draw lists its few thousand values and the other draws filter them, which leaves
# exactly the matches. Bit 31 never reaches rand(): the start states found have it clear, and the
# same state with bit 31 set shows the same draws.

def _bruteforce_starts(plan, cancel=None, progress=None):
    """([start state], cancelled) for every start state with bit 31 clear whose draws show what
    `plan` allows."""
    known, modulus = plan.known, plan.modulus
    if not known:
        raise ValueError("A bruteforce needs at least one known draw.")
    lows = plan.low_candidates()
    # residues[draw][b][q] = 1 when the value 2q + b may be the value of `draw`
    residues = {draw: tuple(bytes(plan.allowed[draw] >> (2 * q + b) & 1 for q in range(modulus))
                            for b in (0, 1)) for draw in known}
    high_muls = [mul & HIGH_MASK for mul, _ in plan.draws]
    inverses = {draw: pow(high_muls[draw], -1, 1 << 14) for draw in known}
    found = []
    if progress is not None:
        progress.total = len(lows)
    for done, low in enumerate(lows):
        if not done & 0xFF:
            if cancel is not None and cancel.is_set():
                return found, True
            if progress is not None:
                progress.done = done
        bits, highs = [], []
        for mul, add in plan.draws:
            draw = (mul * low + add) & MASK32
            bits.append(draw >> 16 & 1)
            highs.append(draw >> 17 & HIGH_MASK)
        order = sorted((sum(residues[draw][bits[draw]]), draw) for draw in known)
        if not order[0][0]:
            continue                        # a draw whose parity is impossible
        pivot = order[0][1]
        inverse, pivot_high, table = inverses[pivot], highs[pivot], residues[pivot][bits[pivot]]
        # u of the pivot draw, then the others as affine functions of it: u_k = factor * u + offset
        candidates = [value for q in range(modulus) if table[q]
                      for value in range(q, 1 << 14, modulus)]
        for _, draw in order[1:]:
            factor = high_muls[draw] * inverse & HIGH_MASK
            offset = (highs[draw] - factor * pivot_high) & HIGH_MASK
            table = residues[draw][bits[draw]]
            candidates = [value for value in candidates
                          if table[(factor * value + offset & HIGH_MASK) % modulus]]
            if not candidates:
                break
        for value in candidates:
            found.append(((value - pivot_high) * inverse & HIGH_MASK) << 17 | low)
    if progress is not None:
        progress.done = len(lows)
    return found, False


def _seek_draws(seed, plan, min_advances, max_advances, cancel, progress, max_results):
    starts, cancelled = _bruteforce_starts(plan, cancel, progress)
    jump_mul, jump_add = plan.to_current
    hits = []
    for start in starts:
        for state in (start, start ^ 0x80000000):      # both show the same draws
            advance = rand_distance(seed, state) + plan.span
            if min_advances <= advance <= max_advances:
                hits.append((advance, (state * jump_mul + jump_add) & MASK32))
    hits.sort()
    status = "cancelled" if cancelled else "done"
    if len(hits) > max_results:
        del hits[max_results:]
        status = "limit"
    return ObservationOutcome(array(U32, (hit[1] for hit in hits)),
                              array(U32, (hit[0] for hit in hits)), status, "seek")


# ------------------------------------------------------------------------------------------------
# Input parsing (the messages are shown to the user)
# ------------------------------------------------------------------------------------------------

def parse_seed(text, label="Initial Seed"):
    digits = text.strip()
    if digits[:2].lower() == "0x":
        digits = digits[2:]
    if not digits:
        raise ValueError(f"Enter the {label} as a hexadecimal value, e.g. 058511BF.")
    if len(digits) > 8 or any(ch not in string.hexdigits for ch in digits):
        raise ValueError(f"{label} must be a 32-bit hexadecimal value (got '{text.strip()}').")
    return int(digits, 16)


def parse_number(text, label, minimum, maximum):
    try:
        value = int(text.strip())
    except ValueError:
        raise ValueError(f"{label} must be a whole number (got '{text.strip()}').") from None
    if not minimum <= value <= maximum:
        raise ValueError(f"{label} must be between {minimum} and {maximum}.")
    return value


def parse_rtc(text, label="Initial RTC"):
    """Seconds since 01/01/2000 00:00:00 of a 'dd/mm/yyyy hh:mm:ss' date and time (the Initial
    RTC field completes a partial one first, see finish_rtc)."""
    try:
        moment = datetime.strptime(" ".join(text.split()), RTC_FORMAT)
    except ValueError:
        raise ValueError(f"{label} must be a date and time like 07/03/2017 22:30:00 "
                         f"(got '{text.strip()}').") from None
    seconds = int((moment - RTC_EPOCH).total_seconds())
    if not 0 <= seconds <= RTC_LAST_SECOND:
        raise ValueError(f"{label} must be between {rtc_text(0)} and {rtc_text(RTC_LAST_SECOND)}.")
    return seconds


def parse_iv_range(stat, min_text, max_text):
    bounds = []
    for label, text in (("Min", min_text), ("Max", max_text)):
        try:
            value = int(text.strip())
        except ValueError:
            value = -1
        if not 0 <= value <= 31:
            raise ValueError(f"{stat} {label} must be a number from 0 to 31 "
                             f"(got '{text.strip()}').")
        bounds.append(value)
    if bounds[0] > bounds[1]:
        raise ValueError(f"{stat}: Min ({bounds[0]}) is greater than Max ({bounds[1]}).")
    return tuple(bounds)


# IV ranges as text, e.g. "0/0/0/0/0/0-31/31/31/31/31/31": the six Min values, a dash, the six Max
# values, in STAT_NAMES order. Spaces around the separators are accepted.
_IV_VALUES_PATTERN = r"\s*/\s*".join([r"(\d{1,2})"] * len(STAT_NAMES))
IV_RANGES_PATTERN = re.compile(rf"\s*{_IV_VALUES_PATTERN}\s*-\s*{_IV_VALUES_PATTERN}\s*")


def iv_ranges_text(ranges):
    """Text form of [(min, max)] per stat (see IV_RANGES_PATTERN)."""
    return "/".join(str(low) for low, _ in ranges) + "-" + "/".join(str(high) for _, high in ranges)


def parse_iv_ranges_text(text):
    """[(min, max)] per stat from the text form, or None if `text` is not in that form or holds a
    value above 31 or a Min greater than its Max."""
    match = IV_RANGES_PATTERN.fullmatch(text)
    if match is None:
        return None
    values = [int(value) for value in match.groups()]
    ranges = list(zip(values[:len(STAT_NAMES)], values[len(STAT_NAMES):]))
    if any(not low <= high <= 31 for low, high in ranges):
        return None
    return ranges


def plural(count, word):
    return f"{count:,} {word}{'' if count == 1 else 's'}"


def input_width(kind):
    """`width` option (in average characters) of an input field that shows the widest value it
    accepts: the font is proportional, so the widest characters are measured, not FFFFFFFF.
    Seeds are sized for their 8 digits: a typed or pasted 0x prefix is removed at once."""
    font = tkfont.nametofont("TkTextFont")
    digit = max(font.measure(character) for character in string.digits)
    pixels = {
        "seed": 8 * max(font.measure(character) for character in string.hexdigits),
        "advances": len(str(MASK32)) * digit,
        "results": len(str(MAX_RESULTS)) * digit,
        "rtc": 14 * digit + font.measure("// ::"),          # dd/mm/yyyy hh:mm:ss
        "iv": 2 * digit,
        "pokemon": len(str(MAX_RANCH_POKEMON)) * digit,
    }[kind]
    return -(-(pixels + 4) // font.measure("0"))            # 4 px for the text cursor


def text_width(texts, font="TkDefaultFont", margin=8):
    """`width` option (in average characters) that fits the widest of `texts`."""
    font = tkfont.nametofont(font)
    return -(-(max(font.measure(text) for text in texts) + margin) // font.measure("0"))


# ------------------------------------------------------------------------------------------------
# Input fields that correct themselves while the user types or pastes
# ------------------------------------------------------------------------------------------------

RTC_PART_DIGITS = (2, 2, 4, 2, 2, 2)    # day, month, year, hour, minute, second
RTC_FIRST_YEAR = RTC_EPOCH.year
RTC_LAST_YEAR = 2036


def clean_hex(text, digits=8):
    """Hexadecimal field: a leading 0x is dropped, only hex digits stay, in upper case; a value
    above the largest one of `digits` digits becomes that largest value."""
    text = text.lstrip()
    if text[:2].lower() == "0x":
        text = text[2:]
    text = "".join(character for character in text if character in string.hexdigits).upper()
    if len(text) > digits:
        value = int(text, 16)
        text = "F" * digits if value >> (4 * digits) else f"{value:0{digits}X}"
    return text


def clean_decimal(text, maximum):
    """Decimal field: only digits stay; a value above `maximum` becomes `maximum`."""
    text = "".join(character for character in text if character in string.digits)
    if text and (int(text) > maximum or len(text) > len(str(maximum))):
        text = str(min(int(text), maximum))
    return text


def rtc_from_parts(parts):
    """'dd/mm/yyyy hh:mm:ss' of day, month, year, hour, minute and second, each brought within
    what the date allows (years 2000-2036)."""
    day, month, year, hour, minute, second = parts
    year = min(max(year, RTC_FIRST_YEAR), RTC_LAST_YEAR)
    month = min(max(month, 1), 12)
    day = min(max(day, 1), calendar.monthrange(year, month)[1])
    hour, minute, second = min(hour, 23), min(minute, 59), min(second, 59)
    return f"{day:02}/{month:02}/{year} {hour:02}:{minute:02}:{second:02}"


RTC_SEPARATORS = str.maketrans(".-", "//")     # other usual date separators
RTC_CHARACTERS = set(string.digits + "/: ")


def clean_rtc(text):
    """Initial RTC field while typing: only digits, '/', ':' and spaces stay ('.' and '-' become
    '/'). Once the six parts are all there (two digits each, four for the year), impossible values
    are corrected and the text takes the dd/mm/yyyy hh:mm:ss form."""
    text = "".join(character for character in text.translate(RTC_SEPARATORS)
                   if character in RTC_CHARACTERS)
    parts = re.findall(r"\d+", text)
    if len(parts) == len(RTC_PART_DIGITS) and all(len(part) >= size
                                                  for part, size in zip(parts, RTC_PART_DIGITS)):
        return rtc_from_parts([int(part) for part in parts])
    return text


def finish_rtc(text):
    """Initial RTC field when it is left: dd/mm/yyyy hh:mm:ss, with a two-digit year read as 20yy
    and a missing time counted as 00:00:00; None when the day, month and year are not all
    there."""
    parts = re.findall(r"\d+", text)[:len(RTC_PART_DIGITS)]
    if len(parts) < 3:
        return None
    values = [int(part) for part in parts] + [0] * (len(RTC_PART_DIGITS) - len(parts))
    if len(parts[2]) <= 2:
        values[2] += 2000
    return rtc_from_parts(values)


FIELD_CLEANERS = {
    "seed": clean_hex,
    "advances": lambda text: clean_decimal(text, MASK32),
    "results": lambda text: clean_decimal(text, MAX_RESULTS),
    "rtc": clean_rtc,
    "iv": lambda text: clean_decimal(text, 31),
    "pokemon": lambda text: clean_decimal(text, MAX_RANCH_POKEMON),
}


def keep_clean(field, variable, clean, on_change=None):
    """Rewrite `variable` with clean(text) after every change of `field` (typing, pasting,
    deleting or a value set by the program), keeping the text cursor by the same characters;
    then call on_change(), if given."""
    busy = False

    def changed(*_):
        nonlocal busy
        if busy:
            return
        text = variable.get()
        cleaned = clean(text)
        if cleaned != text:
            try:
                cursor = field.index("insert")
            except tk.TclError:
                cursor = len(text)
            before = clean(text[:cursor])
            if cleaned.startswith(before):
                position = len(before)
            else:   # rewritten (leading zeros, a corrected date): stay before the same characters
                position = len(cleaned) - len(clean(text[cursor:]))
            busy = True
            try:
                variable.set(cleaned)
            finally:
                busy = False
            field.icursor(min(max(position, 0), len(cleaned)))
        if on_change is not None:
            on_change()

    variable.trace_add("write", changed)


def input_field(master, variable, kind, on_submit=None):
    """ttk.Entry for a value of `kind` (see input_width and FIELD_CLEANERS): sized for the widest
    value it accepts, corrected while the user types or pastes, with undo and redo and the
    right-click menu of the usual text fields (see EditMenu)."""
    field = ttk.Entry(master, textvariable=variable, width=input_width(kind))
    history = FieldHistory(field, variable)
    keep_clean(field, variable, FIELD_CLEANERS[kind], on_change=history.note_change)
    EditMenu.attach(field, history)
    if on_submit is not None:
        field.bind("<Return>", on_submit)
    return field


def stretch_columns(frame):
    """Share the extra width of `frame` among its grid columns in proportion to the width each
    column asks for, so its boxes grow with the window and keep their proportions."""
    frame.update_idletasks()
    for column in range(frame.grid_size()[0]):
        widths = [child.winfo_reqwidth() for child in frame.grid_slaves(column=column)]
        frame.columnconfigure(column, weight=max(widths, default=0))


# ------------------------------------------------------------------------------------------------
# Mouse and keyboard conventions of Windows, macOS and Linux
# ------------------------------------------------------------------------------------------------

def on_macos(widget):
    """True on macOS (Tk's "aqua" windowing system); Windows is "win32", Linux "x11"."""
    return widget.tk.call("tk", "windowingsystem") == "aqua"


def context_click_sequences(widget):
    """Events that ask for a context menu: the right button, which is Button-3, or Button-2 on
    macOS with Tk 8.6; on macOS also Control+click."""
    if on_macos(widget):
        return "<Button-2>", "<Button-3>", "<Control-Button-1>"
    return ("<Button-3>",)


def modifier_click_sequence(widget):
    """Ctrl+click, which is Command+click on macOS (there Control+click is a right-click)."""
    return "<Command-Button-1>" if on_macos(widget) else "<Control-Button-1>"


def shortcut_sequences(widget, letter):
    """Ctrl+letter (either case), and Command+letter too on macOS."""
    modifiers = ("Control", "Command") if on_macos(widget) else ("Control",)
    return tuple(f"<{modifier}-{key}>" for modifier in modifiers
                 for key in (letter.lower(), letter.upper()))


def wheel_notch(widget):
    """<MouseWheel> delta of one wheel notch: 120, but one line on macOS before Tk 8.7."""
    return 1 if on_macos(widget) and tk.TkVersion < 8.7 else 120


def popup_menu(menu, x, y):
    """Open the context `menu` at the screen point (x, y). On Windows and macOS the native menu
    runs until it closes, and the grab Tk may leave behind is released then. On Linux (X11)
    tk_popup returns at once and the menu keeps a grab to close on a click elsewhere: releasing
    it would leave the menu open until one of its entries is chosen."""
    if menu.tk.call("tk", "windowingsystem") == "x11":
        menu.tk_popup(x, y)
        return
    try:
        menu.tk_popup(x, y)
    finally:
        menu.grab_release()


# ------------------------------------------------------------------------------------------------
# Undo, redo and right-click menu of the input fields
# ------------------------------------------------------------------------------------------------

def text_change(old, new):
    """(position, removed text, inserted text) of the one edit that turns `old` into `new`."""
    start, shorter = 0, min(len(old), len(new))
    while start < shorter and old[start] == new[start]:
        start += 1
    end = 0
    while end < shorter - start and old[len(old) - 1 - end] == new[len(new) - 1 - end]:
        end += 1
    return start, old[start:len(old) - end], new[start:len(new) - end]


class FieldHistory:
    """Undo and redo for an input field (a ttk.Entry has neither). The changes made by one event,
    such as a paste over selected text, form one step, and a character typed or deleted right
    after the previous one joins its step, so Undo takes back a whole run of typing."""

    LIMIT = 100                         # steps kept

    def __init__(self, field, variable):
        self._field = field
        self._variable = variable
        self._texts = [variable.get()]  # the text before the first step and after every step
        self._index = 0                 # the step the field shows
        self._join = None               # (kind, position) of a one-character change that joins
        self._pending = None            # after_idle job that records the changes of this event
        self._restoring = False

    def note_change(self):
        """Called after every change of the field's variable (and its correction)."""
        if not self._restoring and self._pending is None:
            self._pending = self._field.after_idle(self._record)

    def can_undo(self):
        self._flush()
        return self._index > 0

    def can_redo(self):
        self._flush()
        return self._index < len(self._texts) - 1

    def undo(self):
        if self.can_undo():
            self._show(self._index - 1)

    def redo(self):
        if self.can_redo():
            self._show(self._index + 1)

    def _flush(self):
        """Record now the changes that wait for the end of their event."""
        if self._pending is not None:
            self._field.after_cancel(self._pending)
            self._record()

    def _record(self):
        self._pending = None
        try:
            text = self._variable.get()
        except tk.TclError:             # the window was closed meanwhile
            return
        previous = self._texts[self._index]
        if text == previous:
            return
        position, removed, inserted = text_change(previous, text)
        if len(inserted) == 1 and not removed:
            kind, follow = "insert", position + 1           # typing goes on after the character
        elif len(removed) == 1 and not inserted:
            kind, follow = "delete", position               # Delete goes on here, Backspace before
        else:
            kind = follow = None
        del self._texts[self._index + 1:]                   # a new change drops what was undone
        join = self._join
        if (kind is not None and join is not None and join[0] == kind and self._index > 0
                and (position == join[1] or (kind == "delete" and position == join[1] - 1))):
            self._texts[self._index] = text
        else:
            self._texts.append(text)
            if len(self._texts) > self.LIMIT:
                del self._texts[0]
            self._index = len(self._texts) - 1
        self._join = None if kind is None else (kind, follow)

    def _show(self, index):
        """Bring the field back to the text of step `index`, the cursor after the edited part."""
        position, _, inserted = text_change(self._texts[self._index], self._texts[index])
        self._index = index
        self._join = None
        self._restoring = True
        try:
            self._variable.set(self._texts[index])
        finally:
            self._restoring = False
        self._field.selection_clear()
        self._field.icursor(position + len(inserted))


class EditMenu:
    """The right-click menu of the input fields, with the entries of the usual text fields:
    Undo, Redo, Cut, Copy, Paste, Delete and Select All. An entry is greyed out when it cannot
    act: Cut, Copy and Delete need selected text, Paste text in the clipboard, Select All text
    not already all selected. One menu per window serves all its fields."""

    def __init__(self, window):
        self.menu = tk.Menu(window, tearoff=False)
        self._field = None
        self._history = None
        self.available = {}             # entry label -> it can act now (set by show())
        keys = self.shortcut_labels(window)
        for label, underline, action in (
                ("Undo", 0, lambda: self._history.undo()),
                ("Redo", 0, lambda: self._history.redo()),
                (None, None, None),
                ("Cut", 2, self._cut),
                ("Copy", 0, self._copy),
                ("Paste", 0, self._paste),
                ("Delete", -1, self._delete),
                (None, None, None),
                ("Select All", -1, self._select_all)):
            if label is None:
                self.menu.add_separator()
            else:
                self.menu.add_command(label=label, underline=underline,
                                      accelerator=keys.get(label, ""),
                                      command=lambda label=label, action=action:
                                      self.available.get(label) and action())

    @staticmethod
    def shortcut_labels(widget):
        """The keys of Tk's <<Undo>>, <<Redo>>, <<Cut>>, ... events on this system, as the menu
        shows them (macOS menus turn "Command-" into the ⌘ symbol)."""
        system = widget.tk.call("tk", "windowingsystem")
        if system == "aqua":
            return {"Undo": "Command-Z", "Redo": "Shift-Command-Z", "Cut": "Command-X",
                    "Copy": "Command-C", "Paste": "Command-V", "Select All": "Command-A"}
        return {"Undo": "Ctrl+Z", "Redo": "Ctrl+Y" if system == "win32" else "Ctrl+Shift+Z",
                "Cut": "Ctrl+X", "Copy": "Ctrl+C", "Paste": "Ctrl+V", "Select All": "Ctrl+A"}

    @classmethod
    def attach(cls, field, history):
        """Give `field` the menu of its window, and Undo / Redo on their usual keys."""
        field.bind("<<Undo>>", lambda event: (history.undo(), "break")[1])
        field.bind("<<Redo>>", lambda event: (history.redo(), "break")[1])
        if field.tk.call("tk", "windowingsystem") == "x11":
            # Ctrl+A moves to the start of the text there (as in Emacs): select all as the menu says
            for sequence in ("<Control-a>", "<Control-A>"):
                field.bind(sequence, lambda event: (cls.select_all(field), "break")[1])

        def show(event):
            window = field.winfo_toplevel()
            menu = getattr(window, "_edit_menu", None)
            if menu is None:
                menu = window._edit_menu = cls(window)
            menu.show(field, history, event.x_root, event.y_root)
            return "break"

        for sequence in context_click_sequences(field):
            field.bind(sequence, show)

    def show(self, field, history, x, y):
        if field.instate(["disabled"]):
            return
        field.focus_set()
        text = field.get()
        selected = field.selection_present()
        all_selected = selected and (field.index("sel.first"),
                                     field.index("sel.last")) == (0, len(text))
        try:
            clipboard = bool(field.clipboard_get())
        except tk.TclError:             # an empty clipboard, or no text in it
            clipboard = False
        self.available = {"Undo": history.can_undo(), "Redo": history.can_redo(),
                          "Cut": selected, "Copy": selected, "Paste": clipboard,
                          "Delete": selected, "Select All": bool(text) and not all_selected}
        theme = getattr(field.winfo_toplevel(), "theme", None)
        colors = theme.colors if theme is not None and theme.colors else None
        if colors is not None:
            self.menu.configure(**menu_colors(colors))
        for label, enabled in self.available.items():
            self._grey_out(label, not enabled, colors)
        self._field, self._history = field, history
        popup_menu(self.menu, x, y)

    def _grey_out(self, label, grey, colors):
        """Show the entry `label` as unavailable or not. Windows draws the text of a disabled
        entry a second time, one pixel lower, in white: invisible on a light menu, a bright
        ghost on a dark one. There the entry stays active instead, in the disabled colour and
        without hover highlight, and its command does nothing (see self.available)."""
        if colors is None or self.menu.tk.call("tk", "windowingsystem") != "win32":
            self.menu.entryconfigure(label, state="disabled" if grey else "normal")
        elif grey:
            self.menu.entryconfigure(label, state="normal",
                                     foreground=colors["menu_disabled_text"],
                                     activeforeground=colors["menu_disabled_text"],
                                     activebackground=colors["menu_background"])
        else:
            self.menu.entryconfigure(label, state="normal", foreground=colors["menu_text"],
                                     activeforeground=colors["menu_active_text"],
                                     activebackground=colors["menu_active_background"])

    def _copy(self):
        field = self._field
        if field.selection_present():
            field.clipboard_clear()
            field.clipboard_append(field.get()[field.index("sel.first"):field.index("sel.last")])

    def _cut(self):
        if self._field.selection_present():
            self._copy()
            self._field.delete("sel.first", "sel.last")

    def _paste(self):
        field = self._field
        try:
            text = field.clipboard_get()
        except tk.TclError:
            return
        if field.selection_present():           # the text replaces the selection
            first = field.index("sel.first")
            field.delete("sel.first", "sel.last")
            field.icursor(first)
        field.insert("insert", text)

    def _delete(self):
        if self._field.selection_present():
            self._field.delete("sel.first", "sel.last")

    def _select_all(self):
        self.select_all(self._field)

    @staticmethod
    def select_all(field):
        field.selection_range(0, "end")
        field.icursor("end")


# ------------------------------------------------------------------------------------------------
# Virtual table widget
# ------------------------------------------------------------------------------------------------

@dataclass(frozen=True)
class ColumnSpec:
    title: str
    sample: str     # widest expected value, used to size the column


DEFAULT_TABLE_COLORS = {        # light colours used until ThemeManager calls apply_colors()
    "table_background": "#FFFFFF", "table_text": "#000000",
    "table_selected": "#0078D7", "table_selected_text": "#FFFFFF",
    "table_border": "#828790", "table_grid": "#D5D5D5",
    "heading_background": "#FFFFFF", "heading_hover": "#D9EBF9", "heading_pressed": "#BCDCF4",
    "heading_text": "#000000",
}


class VirtualTable(ttk.Frame):
    """Read-only grid that stays fast with millions of rows, with cell-range selection.

    Header and body are Canvases that draw a border around every cell; the body draws only the
    lines on screen, so the number of rows does not matter. The table asks for the width of its
    columns at their natural size (title or widest value) and stretches them to fill the width it
    gets. Clicking a heading sorts, dragging the line between two headings moves width from one
    column to the other. The selection is a rectangle of cells:
    click a cell and drag (or Shift+click, Shift+arrows) to extend it. Ctrl+C copies it as
    tab-separated text, a double-click copies the value of the cell under the pointer, and a
    right-click on a row opens the actions registered with add_context_action().

    The model provides len(model), model.row_values(row) -> tuple of strings, and
    model.sort_order(column, descending) -> rows in display order (a range or an array).
    """

    ARROWS = {False: " ▲", True: " ▼"}     # ascending: up, descending: down
    WHEEL_LINES = 3
    RESIZE_MARGIN = 4               # pixels each side of a heading boundary that resize columns
    SHIFT_MASK, CONTROL_MASK = 0x0001, 0x0004

    def __init__(self, master, columns, on_message=None, height=15):
        super().__init__(master)
        self._columns = columns
        self._on_message = on_message or (lambda text: None)
        self._colors = dict(DEFAULT_TABLE_COLORS)

        body_font = tkfont.nametofont("TkDefaultFont")
        heading_font = tkfont.nametofont("TkHeadingFont")
        self._row_height = body_font.metrics("linespace") + 6
        self._header_height = heading_font.metrics("linespace") + 10
        arrow_width = heading_font.measure(self.ARROWS[True])
        # Title (with room for the sort arrow) or widest value, plus a small margin. It is also the
        # minimum width: Canvas text is not clipped, so a narrower column would overlap the next.
        self._min_widths = [max(body_font.measure(column.sample),
                                heading_font.measure(column.title) + arrow_width) + 16
                            for column in columns]
        width = sum(self._min_widths) + 2
        colors = self._colors

        self._header = header = tk.Canvas(self, width=width, height=self._header_height,
                                          background=colors["heading_background"],
                                          highlightthickness=0, borderwidth=0, takefocus=0)
        self._body = body = tk.Canvas(self, width=width, height=height * self._row_height + 1,
                                      background=colors["table_background"],
                                      highlightthickness=0, borderwidth=0, takefocus=1)
        self._scrollbar = ttk.Scrollbar(self, orient="vertical", command=self._on_scrollbar)
        header.grid(row=0, column=0, sticky="ew")
        body.grid(row=1, column=0, sticky="nsew")
        self._scrollbar.grid(row=0, column=1, rowspan=2, sticky="ns")
        self.rowconfigure(1, weight=1)
        self.columnconfigure(0, weight=1)

        # Header: one cell per column, the lines between them, and the frame around them.
        self._heading_cells = [(header.create_rectangle(0, 0, 0, 0, outline=""),
                                header.create_text(0, 0, font="TkHeadingFont"))
                               for _ in columns]
        self._heading_lines = [header.create_line(0, 0, 0, 0, fill=colors["table_grid"])
                               for _ in columns[1:]]
        self._header_frame = [header.create_line(0, 0, 0, 0, fill=colors["table_border"])
                              for _ in range(4)]
        # Body: frame (left, right, bottom), the selection under the cell borders, then the text.
        self._border = [body.create_line(0, 0, 0, 0, fill=colors["table_border"]) for _ in range(3)]
        self._selection_item = body.create_rectangle(0, 0, 0, 0, fill=colors["table_selected"],
                                                     outline="", state="hidden")
        self._column_lines = [body.create_line(0, 0, 0, 0, fill=colors["table_grid"],
                                               state="hidden") for _ in columns[1:]]
        self._row_lines = []            # border under each on-screen line
        self._lines = []                # text items of each on-screen line, one per column
        self._grid_drawn = None         # (lines shown, column boundaries) of the cell borders

        self._column_x = []             # x of the column boundaries (shared by header and body)
        self._widths = []
        # Width beyond the natural one goes to the columns in proportion to these weights: the
        # natural widths at first, the user's choice after a column has been dragged.
        self._weights = list(self._min_widths)
        self._width = width
        self._hover_heading = None
        self._pressed_heading = None
        self._pressed_inside = False
        self._resizing = None           # (boundary, start x, start widths) while resizing
        self._model = None
        self._order = range(0)          # view position -> model row
        self._top = 0                   # view position shown on the first line
        self._capacity = height         # lines that fit on screen
        self._anchor = None             # (view position, column) where the selection starts
        self._cursor = None             # (view position, column) where it ends
        self._sort_column = None        # column showing the arrow, None until a header is clicked
        self._sort_descending = False
        self._dragging = False
        self._wheel_delta = 0
        self._wheel_notch = wheel_notch(self)
        self._context_menu = None       # created by the first add_context_action()
        self._context_values = None     # values of the row the menu was opened on
        self._apply_widths(self._min_widths)
        self._set_line_count(height)
        self._draw_headings()

        for widget in (header, body):
            widget.bind("<MouseWheel>", self._on_wheel)
            widget.bind("<Button-4>", lambda event: self._scroll_by(-self.WHEEL_LINES))   # X11
            widget.bind("<Button-5>", lambda event: self._scroll_by(self.WHEEL_LINES))
        header.bind("<Configure>", self._on_header_configure)
        header.bind("<Motion>", self._on_header_motion)
        header.bind("<Leave>", self._on_header_leave)
        header.bind("<Button-1>", self._on_header_press)
        header.bind("<B1-Motion>", self._on_header_drag)
        header.bind("<ButtonRelease-1>", self._on_header_release)
        body.bind("<Configure>", self._on_body_configure)
        body.bind("<Button-1>", self._on_press)
        body.bind("<B1-Motion>", self._on_drag)
        body.bind("<ButtonRelease-1>", self._on_release)
        body.bind("<Double-Button-1>", self._on_double_click)
        body.bind("<Up>", lambda event: self._on_key_move(event, rows=-1))
        body.bind("<Down>", lambda event: self._on_key_move(event, rows=1))
        body.bind("<Left>", lambda event: self._on_key_move(event, columns=-1))
        body.bind("<Right>", lambda event: self._on_key_move(event, columns=1))
        body.bind("<Prior>", lambda event: self._on_key_move(event, rows=-self._page()))
        body.bind("<Next>", lambda event: self._on_key_move(event, rows=self._page()))
        body.bind("<Home>", lambda event: self._on_key_move(
            event, to_column=0, to_row=0 if event.state & self.CONTROL_MASK else None))
        body.bind("<End>", lambda event: self._on_key_move(
            event, to_column=len(self._columns) - 1,
            to_row=len(self._order) - 1 if event.state & self.CONTROL_MASK else None))
        for sequence in shortcut_sequences(self, "a"):
            body.bind(sequence, self._on_select_all)
        for sequence in shortcut_sequences(self, "c"):
            body.bind(sequence, self._on_copy)
        for sequence in context_click_sequences(self):
            body.bind(sequence, self._on_context_menu)

    # -- public API ------------------------------------------------------------------------------

    def add_context_action(self, label, callback):
        """Add a right-click menu entry for the rows; it calls callback(row values)."""
        if self._context_menu is None:
            self._context_menu = tk.Menu(self, tearoff=False)
        self._context_menu.add_command(label=label,
                                       command=lambda: callback(self._context_values))

    def apply_colors(self, colors):
        """Recolour the table with a ThemeManager colour set."""
        self._colors = {key: colors[key] for key in DEFAULT_TABLE_COLORS}
        body, header = self._body, self._header
        body.configure(background=colors["table_background"])
        header.configure(background=colors["heading_background"])
        body.itemconfigure(self._selection_item, fill=colors["table_selected"])
        for item in self._border:
            body.itemconfigure(item, fill=colors["table_border"])
        for item in self._column_lines + self._row_lines:
            body.itemconfigure(item, fill=colors["table_grid"])
        for item in self._header_frame:
            header.itemconfigure(item, fill=colors["table_border"])
        for item in self._heading_lines:
            header.itemconfigure(item, fill=colors["table_grid"])
        if self._context_menu is not None:
            self._context_menu.configure(**menu_colors(colors))
        self._draw_headings()
        self._refresh()

    def set_model(self, model):
        """Show `model` (None clears the table) in its natural order, without sort arrow."""
        self._model = model
        self._order = range(len(model) if model is not None else 0)
        self._top = 0
        self._anchor = self._cursor = None
        self._sort_column = None
        self._sort_descending = False
        self._dragging = False
        self._draw_headings()
        self._refresh()

    def copy_selection(self):
        """Copy the selected cells as tab-separated lines."""
        bounds = self._selection_bounds()
        if bounds is None:
            return
        first, last, left, right = bounds
        model, order = self._model, self._order
        text = "\n".join("\t".join(model.row_values(order[position])[left:right + 1])
                         for position in range(first, last + 1))
        cells = (last - first + 1) * (right - left + 1)
        self._to_clipboard(text, text if cells == 1 else plural(cells, "cell"))

    # -- layout ----------------------------------------------------------------------------------

    def _apply_widths(self, widths):
        """Place the columns (header and body share the boundaries)."""
        x = 1                           # just inside the left frame line
        boundaries = [x]
        for width in widths:
            x += width
            boundaries.append(x)
        self._widths = list(widths)
        if boundaries != self._column_x:
            self._column_x = boundaries
            self._place_lines()
            self._refresh()
        self._place_header()

    def _fit_columns(self, width):
        """Stretch the columns over the inner `width`: each keeps its natural width and the rest
        is shared by the weights (any rounding leftover goes to the last column)."""
        minimums = self._min_widths
        extra = width - sum(minimums)
        if extra <= 0:
            widths = list(minimums)
        else:
            weights = self._weights if sum(self._weights) > 0 else [1] * len(minimums)
            total = sum(weights)
            widths = [low + extra * weight // total for low, weight in zip(minimums, weights)]
            widths[-1] += width - sum(widths)
        if widths != self._widths:
            self._apply_widths(widths)

    def _on_header_configure(self, event):
        self._width = event.width
        self._place_header()

    def _on_body_configure(self, event):
        left, right, bottom = self._border
        self._body.coords(left, 0, 0, 0, event.height)
        self._body.coords(right, event.width - 1, 0, event.width - 1, event.height)
        self._body.coords(bottom, 0, event.height - 1, event.width, event.height - 1)
        self._fit_columns(event.width - 2)          # inside the left and right frame lines
        capacity = max(1, (event.height - 1) // self._row_height)
        if capacity != self._capacity:
            self._capacity = capacity
            self._set_line_count(capacity)
            self._set_top(self._top, force=True)

    def _set_line_count(self, count):
        body = self._body
        while len(self._lines) < count:
            self._row_lines.append(body.create_line(0, 0, 0, 0, fill=self._colors["table_grid"],
                                                    state="hidden"))
            self._lines.append([body.create_text(0, 0, text="", font="TkDefaultFont")
                                for _ in self._columns])
        while len(self._lines) > count:
            body.delete(self._row_lines.pop())
            for item in self._lines.pop():
                body.delete(item)
        self._grid_drawn = None
        self._place_lines()

    def _place_lines(self):
        height = self._row_height
        centers = [(a + b) // 2 for a, b in zip(self._column_x, self._column_x[1:])]
        for line, items in enumerate(self._lines):
            y = line * height + height // 2
            for item, x in zip(items, centers):
                self._body.coords(item, x, y)

    def _place_header(self):
        header, height, xs, width = self._header, self._header_height, self._column_x, self._width
        for (cell, text), left, right in zip(self._heading_cells, xs, xs[1:]):
            header.coords(cell, left, 1, right, height - 1)
            header.coords(text, (left + right) // 2, height // 2)
        for line, x in zip(self._heading_lines, xs[1:-1]):
            header.coords(line, x - 1, 1, x - 1, height - 1)
        top, left, right, bottom = self._header_frame
        header.coords(top, 0, 0, width, 0)
        header.coords(left, 0, 0, 0, height)
        header.coords(right, width - 1, 0, width - 1, height)
        header.coords(bottom, 0, height - 1, width, height - 1)

    # -- drawing ---------------------------------------------------------------------------------

    def _refresh(self):
        body = self._body
        shown = max(0, min(len(self._lines), len(self._order) - self._top))
        bounds = self._selection_bounds()
        model, order, top = self._model, self._order, self._top
        text_color = self._colors["table_text"]
        selected_text_color = self._colors["table_selected_text"]
        for line, items in enumerate(self._lines):
            if line >= shown:
                for item in items:
                    body.itemconfigure(item, text="")
                continue
            position = top + line
            values = model.row_values(order[position])
            in_rows = bounds is not None and bounds[0] <= position <= bounds[1]
            for column, (item, value) in enumerate(zip(items, values)):
                selected = in_rows and bounds[2] <= column <= bounds[3]
                body.itemconfigure(item, text=value,
                                   fill=selected_text_color if selected else text_color)
        self._draw_grid(shown)
        # One rectangle highlights the part of the selection that is on screen.
        state = "hidden"
        if bounds is not None and shown:
            first, last = max(bounds[0], top), min(bounds[1], top + shown - 1)
            if first <= last:
                body.coords(self._selection_item,
                            self._column_x[bounds[2]], (first - top) * self._row_height,
                            self._column_x[bounds[3] + 1], (last - top + 1) * self._row_height)
                state = "normal"
        body.itemconfigure(self._selection_item, state=state)
        self._update_scrollbar()

    def _draw_grid(self, shown):
        """Borders of the cells on screen: under every line and between the columns."""
        if self._grid_drawn == (shown, self._column_x):
            return
        self._grid_drawn = (shown, self._column_x)
        body, height, right = self._body, self._row_height, self._column_x[-1]
        for line, item in enumerate(self._row_lines):
            if line < shown:
                y = (line + 1) * height - 1
                body.coords(item, 1, y, right, y)
                body.itemconfigure(item, state="normal")
            else:
                body.itemconfigure(item, state="hidden")
        for item, x in zip(self._column_lines, self._column_x[1:-1]):
            body.coords(item, x - 1, 0, x - 1, shown * height)
            body.itemconfigure(item, state="normal" if shown else "hidden")

    def _draw_headings(self):
        colors = self._colors
        for index, ((cell, text), column) in enumerate(zip(self._heading_cells, self._columns)):
            title = column.title
            if index == self._sort_column:
                title += self.ARROWS[self._sort_descending]
            if index == self._pressed_heading and self._pressed_inside:
                fill = colors["heading_pressed"]
            elif index == self._hover_heading and self._pressed_heading is None:
                fill = colors["heading_hover"]
            else:
                fill = colors["heading_background"]
            self._header.itemconfigure(cell, fill=fill)
            self._header.itemconfigure(text, text=title, fill=colors["heading_text"])

    def _update_scrollbar(self):
        count = len(self._order)
        if count == 0:
            self._scrollbar.set(0.0, 1.0)
        else:
            self._scrollbar.set(self._top / count, min(1.0, (self._top + self._capacity) / count))

    # -- header: hover, sorting clicks, column resizing ------------------------------------------

    def _boundary_at(self, x):
        """Column whose right edge, shared with the next column, is under x, or None (the right
        edge of the last column is the edge of the table)."""
        for column in range(len(self._columns) - 1):
            if abs(x - (self._column_x[column + 1] - 1)) <= self.RESIZE_MARGIN:
                return column
        return None

    def _heading_at(self, x):
        column = bisect.bisect_right(self._column_x, x) - 1
        return column if 0 <= column < len(self._columns) else None

    def _on_header_motion(self, event):
        if self._resizing is not None or self._pressed_heading is not None:
            return
        boundary = self._boundary_at(event.x)
        self._header.configure(cursor="sb_h_double_arrow" if boundary is not None else "")
        hover = None if boundary is not None else self._heading_at(event.x)
        if hover != self._hover_heading:
            self._hover_heading = hover
            self._draw_headings()

    def _on_header_leave(self, event):
        if self._resizing is None and self._pressed_heading is None:
            self._header.configure(cursor="")
            if self._hover_heading is not None:
                self._hover_heading = None
                self._draw_headings()

    def _on_header_press(self, event):
        edge = self._boundary_at(event.x)
        if edge is not None:
            self._resizing = (edge, event.x, list(self._widths))
            return
        self._pressed_heading = self._heading_at(event.x)
        self._pressed_inside = self._pressed_heading is not None
        self._draw_headings()

    def _on_header_drag(self, event):
        if self._resizing is not None:
            # The column on the left of the line gets what the one on its right gives, so the
            # table keeps its width; neither goes below its natural width.
            column, start_x, start = self._resizing
            minimums = self._min_widths
            shift = min(max(event.x - start_x, minimums[column] - start[column]),
                        start[column + 1] - minimums[column + 1])
            widths = list(start)
            widths[column] += shift
            widths[column + 1] -= shift
            if widths != self._widths:
                self._weights = [width - low for width, low in zip(widths, minimums)]
                self._apply_widths(widths)
        elif self._pressed_heading is not None:
            inside = (self._heading_at(event.x) == self._pressed_heading
                      and 0 <= event.y < self._header_height)
            if inside != self._pressed_inside:
                self._pressed_inside = inside
                self._draw_headings()

    def _on_header_release(self, event):
        if self._resizing is not None:
            self._resizing = None
            return
        column, inside = self._pressed_heading, self._pressed_inside
        self._pressed_heading = None
        self._pressed_inside = False
        self._draw_headings()
        if column is not None and inside:
            self._on_heading(column)

    # -- scrolling -------------------------------------------------------------------------------

    def _page(self):
        return max(1, self._capacity - 1)

    def _set_top(self, top, force=False):
        top = max(0, min(top, len(self._order) - self._capacity))
        if force or top != self._top:
            self._top = top
            self._refresh()

    def _scroll_by(self, lines):
        self._set_top(self._top + lines)
        return "break"

    def _ensure_visible(self, position):
        if position < self._top:
            self._top = position
        elif position >= self._top + self._capacity:
            self._top = position - self._capacity + 1

    def _on_scrollbar(self, action, value, unit=None):
        if action == "moveto":
            self._set_top(round(float(value) * len(self._order)))
        elif action == "scroll":
            self._set_top(self._top + int(value) * (self._page() if unit == "pages" else 1))

    def _on_wheel(self, event):
        self._wheel_delta += event.delta
        notches = int(self._wheel_delta / self._wheel_notch)
        if notches:
            self._wheel_delta -= notches * self._wheel_notch
            # A notch of 120 scrolls WHEEL_LINES lines; a delta in lines (macOS, Tk 8.6) as many.
            self._scroll_by(-notches * (self.WHEEL_LINES if self._wheel_notch == 120 else 1))
        return "break"

    # -- selection -------------------------------------------------------------------------------

    def _selection_bounds(self):
        """(first position, last position, first column, last column) or None."""
        if self._anchor is None or self._cursor is None:
            return None
        (row_a, column_a), (row_b, column_b) = self._anchor, self._cursor
        return (min(row_a, row_b), max(row_a, row_b),
                min(column_a, column_b), max(column_a, column_b))

    def _cell_at(self, x, y, clamp=False):
        """(view position, column) under the point, or None; `clamp` keeps it inside the data."""
        shown = min(self._capacity, len(self._order) - self._top)
        if shown <= 0:
            return None
        line = y // self._row_height
        column = bisect.bisect_right(self._column_x, x) - 1
        if clamp:
            line = max(0, min(shown - 1, line))
            column = max(0, min(len(self._columns) - 1, column))
        elif not (0 <= line < shown and 0 <= column < len(self._columns)):
            return None
        return self._top + line, column

    def _on_press(self, event):
        self._body.focus_set()
        cell = self._cell_at(event.x, event.y)
        if cell is None:
            return "break"
        if event.state & self.SHIFT_MASK and self._anchor is not None:
            self._cursor = cell
        else:
            self._anchor = self._cursor = cell
        self._dragging = True
        self._refresh()
        return "break"

    def _on_drag(self, event):
        if not self._dragging:
            return "break"
        if event.y < 0:                 # past the top or bottom edge: scroll one line
            self._set_top(self._top - 1)
        elif event.y >= self._capacity * self._row_height:
            self._set_top(self._top + 1)
        cell = self._cell_at(event.x, event.y, clamp=True)
        if cell is not None and cell != self._cursor:
            self._cursor = cell
            self._refresh()
        return "break"

    def _on_release(self, event):
        self._dragging = False
        return "break"

    def _on_key_move(self, event, rows=0, columns=0, to_row=None, to_column=None):
        count = len(self._order)
        if count == 0:
            return "break"
        if self._cursor is None:        # the first key press only activates the top-left cell
            position, column = self._top, 0
        else:
            position, column = self._cursor
            position = to_row if to_row is not None else position + rows
            column = to_column if to_column is not None else column + columns
        cell = (max(0, min(count - 1, position)), max(0, min(len(self._columns) - 1, column)))
        if event.state & self.SHIFT_MASK and self._anchor is not None:
            self._cursor = cell
        else:
            self._anchor = self._cursor = cell
        self._ensure_visible(cell[0])
        self._set_top(self._top, force=True)
        return "break"

    def _on_select_all(self, event=None):
        if len(self._order):
            self._anchor = (0, 0)
            self._cursor = (len(self._order) - 1, len(self._columns) - 1)
            self._refresh()
        return "break"

    # -- copy and context menu -------------------------------------------------------------------

    def _on_copy(self, event=None):
        self.copy_selection()
        return "break"

    def _on_double_click(self, event):
        cell = self._cell_at(event.x, event.y)
        if cell is not None:
            position, column = cell
            value = self._model.row_values(self._order[position])[column]
            self._anchor = self._cursor = cell      # the copied cell is the selection
            self._refresh()
            self._to_clipboard(value, value)
        return "break"

    def _to_clipboard(self, text, description):
        self.clipboard_clear()
        self.clipboard_append(text)
        self._on_message(f"Copied {description} to the clipboard")

    def _on_context_menu(self, event):
        cell = self._cell_at(event.x, event.y)
        if self._context_menu is None or cell is None:
            return "break"              # no actions, or not on a row
        self._body.focus_set()
        position, column = cell
        bounds = self._selection_bounds()
        if (bounds is None or not bounds[0] <= position <= bounds[1]
                or not bounds[2] <= column <= bounds[3]):
            self._anchor = self._cursor = cell      # outside the selection: select the cell first
            self._refresh()
        self._context_values = self._model.row_values(self._order[position])
        popup_menu(self._context_menu, event.x_root, event.y_root)
        return "break"

    # -- sorting ---------------------------------------------------------------------------------

    def _on_heading(self, column):
        # The first click on a column sorts ascending, every further click flips the direction.
        descending = not self._sort_descending if column == self._sort_column else False
        self._body.configure(cursor="watch")
        self._body.update_idletasks()
        try:
            if self._model is not None:
                self._order = self._model.sort_order(column, descending)
            self._sort_column = column
            self._sort_descending = descending
            self._anchor = self._cursor = None      # a cell range means nothing in the new order
            self._draw_headings()
            self._top = 0
            self._refresh()
        finally:
            self._body.configure(cursor="")


# ------------------------------------------------------------------------------------------------
# Result models
# ------------------------------------------------------------------------------------------------

IV_COLUMNS = [ColumnSpec(name, "31") for name in STAT_NAMES]


def iv_values(ivs):
    return [str((ivs >> shift) & 31) for shift in STAT_SHIFTS]


def iv_sort_order(ivs, stat, descending):
    """Rows sorted by one IV (index in STAT_NAMES); equal values keep the stored row order."""
    shift = STAT_SHIFTS[stat]
    buckets = [array(U32) for _ in range(32)]       # counting sort on the 32 possible values
    push = [bucket.append for bucket in buckets]
    for row, word in enumerate(ivs):
        push[(word >> shift) & 31](row)
    if descending:
        buckets.reverse()
    order = array(U32)
    for bucket in buckets:
        order.extend(bucket)
    return order


class GeneratorResults:
    """Generator rows, stored in ascending advance order."""

    COLUMNS = [ColumnSpec("Current Seed", "DDDDDDDD"),
               ColumnSpec("Advances", "4294967295")] + IV_COLUMNS
    SEED_COLUMN, ADVANCES_COLUMN, FIRST_IV_COLUMN = 0, 1, 2

    def __init__(self, outcome):
        self._seeds = outcome.seeds
        self._advances = outcome.advances
        self._ivs = outcome.ivs

    def __len__(self):
        return len(self._seeds)

    def row_values(self, row):
        return (f"{self._seeds[row]:08X}", str(self._advances[row]), *iv_values(self._ivs[row]))

    def sort_order(self, column, descending):
        count = len(self)
        if column == self.ADVANCES_COLUMN:
            return range(count - 1, -1, -1) if descending else range(count)
        if column == self.SEED_COLUMN:      # seeds are all different within one search
            return array(U32, sorted(range(count), key=self._seeds.__getitem__, reverse=descending))
        return iv_sort_order(self._ivs, column - self.FIRST_IV_COLUMN, descending)


class SearcherResults:
    """Searcher rows, stored in ascending seed order."""

    COLUMNS = [ColumnSpec("Seed", "DDDDDDDD")] + IV_COLUMNS
    SEED_COLUMN, FIRST_IV_COLUMN = 0, 1

    def __init__(self, outcome):
        self._seeds = outcome.seeds
        self._ivs = outcome.ivs

    def __len__(self):
        return len(self._seeds)

    def row_values(self, row):
        return (f"{self._seeds[row]:08X}", *iv_values(self._ivs[row]))

    def sort_order(self, column, descending):
        count = len(self)
        if column == self.SEED_COLUMN:
            return range(count - 1, -1, -1) if descending else range(count)
        return iv_sort_order(self._ivs, column - self.FIRST_IV_COLUMN, descending)


class RtcResults:
    """Seed to RTC rows, stored in ascending RTC order."""

    COLUMNS = [ColumnSpec("Initial Seed", "DDDDDDDD"), ColumnSpec("Advances", "4294967295"),
               ColumnSpec("RTC", "31/12/2036 23:59:59")]
    SEED_COLUMN, ADVANCES_COLUMN, RTC_COLUMN = 0, 1, 2

    def __init__(self, outcome):
        self._seconds = outcome.seconds
        self._seeds = outcome.seeds
        self._advances = outcome.advances

    def __len__(self):
        return len(self._seconds)

    def row_values(self, row):
        return f"{self._seeds[row]:08X}", str(self._advances[row]), rtc_text(self._seconds[row])

    def sort_order(self, column, descending):
        count = len(self)
        if column == self.RTC_COLUMN:
            return range(count - 1, -1, -1) if descending else range(count)
        values = self._seeds if column == self.SEED_COLUMN else self._advances
        # sorted() is stable also with reverse=True: equal values stay in RTC order.
        return array(U32, sorted(range(count), key=values.__getitem__, reverse=descending))


class ObservationResults:
    """Seed from Camera / Dex / Dice rows, stored in ascending advance order (ascending seed
    order after a bruteforce, which has no advances). The last column, the next entries the game
    will show, is computed when a row is displayed."""

    COLUMNS = ()
    SEED_COLUMN, ADVANCES_COLUMN, NEXT_COLUMN = 0, 1, 2

    def __init__(self, outcome):
        self._seeds = outcome.seeds
        self._advances = outcome.advances
        self._next = {}

    def __len__(self):
        return len(self._seeds)

    def _predict(self, row):
        raise NotImplementedError

    def next_text(self, row):
        text = self._next.get(row)
        if text is None:
            text = self._next[row] = self._predict(row)
        return text

    def row_values(self, row):
        advances = "" if self._advances is None else str(self._advances[row])
        return f"{self._seeds[row]:08X}", advances, self.next_text(row)

    def sort_order(self, column, descending):
        count = len(self)
        natural = self.SEED_COLUMN if self._advances is None else self.ADVANCES_COLUMN
        if column == natural:
            return range(count - 1, -1, -1) if descending else range(count)
        if column == self.SEED_COLUMN:
            key = self._seeds.__getitem__
        elif column == self.NEXT_COLUMN:
            key = self.next_text
        else:
            return range(count)             # the empty Advances of a bruteforce
        return array(U32, sorted(range(count), key=key, reverse=descending))


class CameraResults(ObservationResults):
    COLUMNS = [ColumnSpec("Current Seed", "DDDDDDDD"), ColumnSpec("Advances", "4294967295"),
               ColumnSpec("Next Cameras", " → ".join(["Up + Zoom In"] * CAMERA_PREDICTIONS))]

    def _predict(self, row):
        return predicted_cameras(self._seeds[row])


class DexResults(ObservationResults):
    COLUMNS = [ColumnSpec("Current Seed", "DDDDDDDD"), ColumnSpec("Advances", "4294967295"),
               ColumnSpec("Next Descriptions", " → ".join(["D/P"] * DEX_PREDICTIONS))]

    def __init__(self, outcome, version):
        super().__init__(outcome)
        self._version = version         # the build the search was made for

    def _predict(self, row):
        return predicted_descriptions(self._seeds[row], self._version)


class DiceResults(ObservationResults):
    COLUMNS = [ColumnSpec("Current Seed", "DDDDDDDD"), ColumnSpec("Advances", "4294967295"),
               ColumnSpec("Next Rolls", " → ".join(["6"] * DICE_PREDICTIONS))]

    def _predict(self, row):
        return predicted_rolls(self._seeds[row])


# ------------------------------------------------------------------------------------------------
# Settings kept between sessions
# ------------------------------------------------------------------------------------------------

def application_path():
    """Path of this program: the script, or the executable when it is packaged (PyInstaller)."""
    if getattr(sys, "frozen", False):
        return sys.executable
    return os.path.abspath(__file__)


class AppSettings:
    """Values remembered in an .ini file with the program's own name, next to it (made at the first
    launch): ranch_rng_tool.ini for ranch_rng_tool.py, MyTool.ini for a copy named MyTool.py."""

    PATH = os.path.splitext(application_path())[0] + ".ini"
    SECTION = "Seed RTC"
    APPEARANCE = "Appearance"

    def __init__(self, path=PATH):
        self._path = path
        self._parser = configparser.ConfigParser()
        try:
            self._parser.read(path, encoding="utf-8")
        except (configparser.Error, UnicodeDecodeError):
            self._parser = configparser.ConfigParser()      # unreadable file: start again
        for section in (self.SECTION, self.APPEARANCE):
            if not self._parser.has_section(section):
                self._parser.add_section(section)
        if not os.path.exists(path):
            self._parser.set(self.SECTION, "origin_seed", f"{DEFAULT_ORIGIN_SEED:08X}")
            self._parser.set(self.APPEARANCE, "theme", DEFAULT_THEME)
            self.save()

    @property
    def theme(self):
        name = self._parser.get(self.APPEARANCE, "theme", fallback=DEFAULT_THEME)
        return name if name in THEMES else DEFAULT_THEME

    @theme.setter
    def theme(self, name):
        if self._parser.get(self.APPEARANCE, "theme", fallback=None) != name:
            self._parser.set(self.APPEARANCE, "theme", name)
            self.save()

    @property
    def origin_seed(self):
        try:
            return parse_seed(self._parser.get(self.SECTION, "origin_seed", fallback=""),
                              "Origin Seed")
        except ValueError:
            return DEFAULT_ORIGIN_SEED

    @origin_seed.setter
    def origin_seed(self, seed):
        text = f"{seed:08X}"
        if self._parser.get(self.SECTION, "origin_seed", fallback=None) != text:
            self._parser.set(self.SECTION, "origin_seed", text)
            self.save()

    def save(self):
        try:
            with open(self._path, "w", encoding="utf-8") as file:
                self._parser.write(file)
        except OSError:
            pass            # e.g. a read-only folder: the values are simply not remembered


# ------------------------------------------------------------------------------------------------
# Images drawn by the program (PNG data for tk.PhotoImage, no image files needed)
# ------------------------------------------------------------------------------------------------

def rgba_png(width, height, pixels):
    """Base64 PNG of `pixels`: for every line a 0 byte (no PNG filter) and `width` RGBA pixels."""
    def chunk(kind, payload):
        return (struct.pack(">I", len(payload)) + kind + payload
                + struct.pack(">I", zlib.crc32(kind + payload)))

    header = struct.pack(">IIBBBBB", width, height, 8, 6, 0, 0, 0)  # 8 bits per channel, RGBA
    png = (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", header)
           + chunk(b"IDAT", zlib.compress(bytes(pixels))) + chunk(b"IEND", b""))
    return base64.b64encode(png).decode("ascii")


def coverage(distance_inside):
    """Opacity of a pixel whose centre lies `distance_inside` pixels inside a shape's edge (a
    negative value: outside), so that the edges look smooth."""
    return min(1.0, max(0.0, distance_inside + 0.5))


# Pips of the die faces as (column, row) on a 3 x 3 grid: the 2 and the 3 run from the top left
# corner to the bottom right one, the 6 is two columns of three.
DIE_PIPS = {
    1: ((1, 1),),
    2: ((0, 0), (2, 2)),
    3: ((0, 0), (1, 1), (2, 2)),
    4: ((0, 0), (2, 0), (0, 2), (2, 2)),
    5: ((0, 0), (2, 0), (1, 1), (0, 2), (2, 2)),
    6: ((0, 0), (0, 1), (0, 2), (2, 0), (2, 1), (2, 2)),
}


def die_face_png(face, size, color):
    """Base64 PNG of the pips of a die face: filled dots of `color` ("#RRGGBB") on a transparent
    size x size square."""
    red, green, blue = (int(color[index:index + 2], 16) for index in (1, 3, 5))
    radius = 0.1 * size
    centers = [(size * (0.2 + 0.3 * column), size * (0.2 + 0.3 * row))
               for column, row in DIE_PIPS[face]]
    pixels = bytearray()
    for y in range(size):
        pixels.append(0)
        for x in range(size):
            distance = min(math.hypot(x + 0.5 - cx, y + 0.5 - cy) for cx, cy in centers)
            pixels += bytes((red, green, blue, round(255 * coverage(radius - distance))))
    return rgba_png(size, size, pixels)


ERROR_RED = (0xE8, 0x11, 0x23)          # the red of the Windows error icon


def error_icon_png(size):
    """Base64 PNG of the error icon of a message: a white cross on a red disc, size x size."""
    center = size / 2
    radius = center - 0.5
    arm = 0.22 * size                   # each stroke of the cross runs from -arm to +arm
    half_width = 0.055 * size
    pixels = bytearray()
    for y in range(size):
        pixels.append(0)
        for x in range(size):
            dx, dy = x + 0.5 - center, y + 0.5 - center
            cross = 0.0
            for sign in (1, -1):        # the strokes along (1, 1) and (1, -1)
                along = min(arm, max(-arm, (dx + sign * dy) / 2))
                cross = max(cross, coverage(half_width - math.hypot(dx - along, dy - sign * along)))
            red, green, blue = (round(channel + (255 - channel) * cross) for channel in ERROR_RED)
            pixels += bytes((red, green, blue, round(255 * coverage(radius - math.hypot(dx, dy)))))
    return rgba_png(size, size, pixels)


def segment_distance(x, y, start, end):
    """Distance of the point (x, y) from the segment between the points `start` and `end`."""
    (ax, ay), (bx, by) = start, end
    dx, dy = bx - ax, by - ay
    along = max(0.0, min(1.0, ((x - ax) * dx + (y - ay) * dy) / (dx * dx + dy * dy)))
    return math.hypot(x - ax - along * dx, y - ay - along * dy)


CHECK_MARK = ((0.22, 0.53), (0.42, 0.73), (0.80, 0.29))     # the ✓ line, in box sizes


def check_box_png(size, margins, border, fill, mark=None):
    """Base64 PNG of a check box: a size x size square, a one-pixel `border` around `fill`, with
    a check mark of colour `mark` (None: an empty box) and transparent `margins` (left, top,
    right, bottom) around it. The colours are "#RRGGBB"."""
    def rgb(color):
        return tuple(int(color[index:index + 2], 16) for index in (1, 3, 5))

    left, top, right, bottom = margins
    edge, inside = rgb(border) + (255,), rgb(fill)
    points = [(x * size, y * size) for x, y in CHECK_MARK]
    half_width = max(0.8, 0.075 * size)
    pixels = bytearray()
    for y in range(top + size + bottom):
        pixels.append(0)
        for x in range(left + size + right):
            bx, by = x - left, y - top
            if not (0 <= bx < size and 0 <= by < size):
                pixels += bytes(4)                          # transparent margin
            elif bx in (0, size - 1) or by in (0, size - 1):
                pixels += bytes(edge)
            else:
                ink = 0.0
                if mark is not None:
                    ink = coverage(half_width - min(segment_distance(bx + 0.5, by + 0.5, a, b)
                                                    for a, b in zip(points, points[1:])))
                color = inside if ink == 0.0 else tuple(
                    round(f + (m - f) * ink) for f, m in zip(inside, rgb(mark)))
                pixels += bytes(color + (255,))
    return rgba_png(left + size + right, top + size + bottom, pixels)


# ------------------------------------------------------------------------------------------------
# Tabs
# ------------------------------------------------------------------------------------------------

class IvRangeFrame(ttk.LabelFrame):
    """Min/Max spinboxes for the six IVs. A click on a stat's name sets its range to 0-31 (any
    value), a Ctrl+click (Command+click on macOS) to 31-31. A right-click anywhere in the frame
    opens a menu that copies, pastes (as "0/0/0/0/0/0-31/31/31/31/31/31"), clears or maxes out all
    the ranges; on_message(text) shows a short confirmation."""

    def __init__(self, master, on_submit=None, on_message=None):
        super().__init__(master, text="IVs", padding=(10, 6))
        self.grid_anchor("center")      # vertically centred when the box beside it is taller
        self._on_message = on_message
        ttk.Label(self, text="Min").grid(row=1, column=0, sticky="w", padx=(0, 6))
        ttk.Label(self, text="Max").grid(row=2, column=0, sticky="w", padx=(0, 6))
        self.min_vars, self.max_vars = [], []
        for column, name in enumerate(STAT_NAMES, start=1):
            label = ttk.Label(self, text=name, cursor="hand2")
            label.grid(row=0, column=column)
            # Tk runs the most specific binding: the modifier one when the modifier is held
            label.bind("<Button-1>", lambda event, index=column - 1: self.set_range(index, 0, 31))
            label.bind(modifier_click_sequence(self),
                       lambda event, index=column - 1: self.set_range(index, 31, 31))
            self.columnconfigure(column, weight=1)      # the spinboxes widen with the frame
            for row, (default, variables) in enumerate((("0", self.min_vars),
                                                        ("31", self.max_vars)), start=1):
                variable = tk.StringVar(value=default)
                spinbox = ttk.Spinbox(self, from_=0, to=31, width=input_width("iv"),
                                      justify="center", textvariable=variable)
                spinbox.grid(row=row, column=column, padx=2, pady=2, sticky="ew")
                keep_clean(spinbox, variable, FIELD_CLEANERS["iv"])
                if on_submit is not None:
                    spinbox.bind("<Return>", on_submit)
                variables.append(variable)
        self.menu = tk.Menu(self, tearoff=False)
        self.menu.add_command(label="Copy IVs to clipboard", command=self.copy_ranges)
        self.menu.add_command(label="Paste IVs from clipboard", command=self.paste_ranges)
        self.menu.add_command(label="Clear IVs", command=lambda: self.set_all(0, 31))
        self.menu.add_command(label="Set 6IVs", command=lambda: self.set_all(31, 31))
        for widget in (self, *self.winfo_children()):
            if widget is not self.menu:
                for sequence in context_click_sequences(self):
                    widget.bind(sequence, self._show_menu)

    def set_range(self, index, low, high):
        """Min and Max of the stat at `index` in STAT_NAMES."""
        self.min_vars[index].set(str(low))
        self.max_vars[index].set(str(high))

    def set_all(self, low, high):
        """The same Min and Max for every stat."""
        for index in range(len(STAT_NAMES)):
            self.set_range(index, low, high)

    def ranges(self):
        """(min, max) per stat in STAT_NAMES order; raises ValueError with a readable message."""
        return [parse_iv_range(name, low.get(), high.get())
                for name, low, high in zip(STAT_NAMES, self.min_vars, self.max_vars)]

    def apply_colors(self, colors):
        self.menu.configure(**menu_colors(colors))

    def _show_menu(self, event):
        popup_menu(self.menu, event.x_root, event.y_root)
        return "break"

    def copy_ranges(self):
        try:
            text = iv_ranges_text(self.ranges())
        except ValueError as error:
            show_error(self, "Invalid input", str(error))
            return
        self.clipboard_clear()
        self.clipboard_append(text)
        if self._on_message is not None:
            self._on_message(f"Copied {text} to the clipboard")

    def paste_ranges(self):
        try:
            ranges = parse_iv_ranges_text(self.clipboard_get())
        except tk.TclError:             # empty clipboard, or no text in it
            ranges = None
        if ranges is None:
            show_error(self, "Invalid input",
                       "The clipboard text did not match the expected format.")
            return
        for index, (low, high) in enumerate(ranges):
            self.set_range(index, low, high)
        if self._on_message is not None:
            self._on_message(f"Pasted {iv_ranges_text(ranges)} from the clipboard")


TRADE_OFFSET_WIDTH = max(len(choice) for choice in TRADE_OFFSET_CHOICES)  # drop-down, characters


class TradeOffsetOption:
    """"Trade Offset" check box (on at start), gridded in `master` at (row, column), with the
    Accepted / Refused drop-down on its right. On the next row the version (JPN Pt or GER), and
    on the one after it the number of Pokémon on the ranch, which the JPN Pt offsets depend on.
    What does not apply is greyed out: everything but the box while it is off, the number of
    Pokémon with GER."""

    def __init__(self, master, row, column, on_submit=None):
        self.enabled_var = tk.BooleanVar(value=True)
        self.choice_var = tk.StringVar(value=TRADE_OFFSET_CHOICES[0])
        self.version_var = tk.StringVar(value=DEFAULT_TRADE_OFFSET_VERSION)
        self.pokemon_var = tk.StringVar(value=str(DEFAULT_RANCH_POKEMON))
        indent = 16 if column else 0        # the labels of a second column of fields
        self.check = ttk.Checkbutton(master, text="Trade Offset", variable=self.enabled_var,
                                     command=self._sync_state)
        self.check.grid(row=row, column=column, sticky="w", padx=(indent, 8), pady=4)
        self.combobox = ttk.Combobox(master, textvariable=self.choice_var,
                                     values=TRADE_OFFSET_CHOICES, width=TRADE_OFFSET_WIDTH)
        self.combobox.grid(row=row, column=column + 1, sticky="ew", pady=4)
        versions = ttk.Frame(master)
        versions.grid(row=row + 1, column=column, columnspan=2, sticky="w", padx=(indent, 0),
                      pady=2)
        self.version_buttons = []
        for index, name in enumerate(TRADE_OFFSET_VERSIONS):
            button = ttk.Radiobutton(versions, text=name, value=name, variable=self.version_var,
                                     command=self._sync_state)
            button.grid(row=0, column=index, padx=(0, 12))
            self.version_buttons.append(button)
        self.pokemon_label = ttk.Label(master, text="Ranch Pokémon")
        self.pokemon_label.grid(row=row + 2, column=column, sticky="w", padx=(indent, 8), pady=4)
        self.pokemon_field = input_field(master, self.pokemon_var, "pokemon", on_submit)
        self.pokemon_field.grid(row=row + 2, column=column + 1, sticky="ew", pady=4)
        if on_submit is not None:
            self.combobox.bind("<Return>", on_submit)
        self._sync_state()

    def _sync_state(self):
        enabled = self.enabled_var.get()
        self.combobox.configure(state="readonly" if enabled else "disabled")
        for button in self.version_buttons:
            button.state(["!disabled" if enabled else "disabled"])
        pokemon = enabled and self.version_var.get() == "JPN Pt"
        for widget in (self.pokemon_label, self.pokemon_field):
            widget.state(["!disabled" if pokemon else "disabled"])

    def offset(self):
        """rand() calls between the shown seed and the IVs: 0 while the option is off. Raises
        ValueError with a message for the user when JPN Pt lacks the number of Pokémon."""
        if not self.enabled_var.get():
            return 0
        version = self.version_var.get()
        pokemon = 0
        if CALLS_PER_RANCH_POKEMON[version]:
            text = self.pokemon_var.get().strip()
            if not text:
                raise ValueError(f"Enter the number of Pokémon on the ranch in Ranch Pokémon: "
                                 f"the {version} Trade Offset depends on it.")
            pokemon = parse_number(text, "Ranch Pokémon", 0, MAX_RANCH_POKEMON)
        return trade_offset(self.choice_var.get(), version, pokemon)

    def apply_colors(self, colors):
        """Recolour the drop-down list after a theme switch, if Tk has already created it (a list
        created later takes its colours from the option database, see ThemeManager). It must not
        be created here: on Windows it is a topmost window, and created before the main window is
        first shown it makes the main window stay on top of the others too."""
        listbox = f"{self.combobox}.popdown.f.l"
        if self.combobox.winfo_exists() and self.combobox.tk.call("winfo", "exists", listbox):
            self.combobox.tk.call(listbox, "configure",
                                  "-background", colors["list_background"],
                                  "-foreground", colors["list_text"],
                                  "-selectbackground", colors["list_selected"],
                                  "-selectforeground", colors["list_selected_text"])


class SearchTab(ttk.Frame):
    """Inputs on top, a results table and a status bar; the search runs on a worker thread.

    Subclasses define COLUMNS (and optionally SEARCH_LABEL) and implement _build_inputs,
    _read_inputs, _search (worker thread) and _present.
    """

    POLL_MS = 100
    COLUMNS = ()
    SEARCH_LABEL = "Search"

    def __init__(self, master):
        super().__init__(master, padding=8)
        self._worker = None
        self._cancel = None
        self._progress = None
        self._outcome = None
        self._error = None
        self._summary = "Ready"         # status text shown again after a temporary message
        self._flash_job = None

        # Row 0: inputs, whose boxes share the width of the window. Row 1: results table, filling
        # the rest of the tab. Row 2: Search and Cancel side by side under the table, on the left.
        # Row 3: status bar.
        top = ttk.Frame(self)
        top.grid(row=0, column=0, sticky="ew")
        self._build_inputs(top)
        stretch_columns(top)
        buttons = ttk.Frame(self)           # created before the table: Tab reaches it first
        buttons.grid(row=2, column=0, sticky="w", pady=(6, 0))
        self.search_button = ttk.Button(buttons, text=self.SEARCH_LABEL, command=self.start_search)
        self.search_button.grid(row=0, column=0, padx=(0, 6))
        self.cancel_button = ttk.Button(buttons, text="Cancel", command=self.cancel_search,
                                        state="disabled")
        self.cancel_button.grid(row=0, column=1)

        self.table = VirtualTable(self, self.COLUMNS, on_message=self.flash_status)
        self.table.grid(row=1, column=0, sticky="nsew", pady=(8, 0))

        bar = ttk.Frame(self)
        bar.grid(row=3, column=0, sticky="ew", pady=(6, 0))
        self.status_var = tk.StringVar(value=self._summary)
        status_label = ttk.Label(bar, textvariable=self.status_var)
        status_label.grid(row=0, column=0, sticky="w")
        self.progress_bar = ttk.Progressbar(bar, mode="determinate", length=200)
        self.progress_bar.grid(row=0, column=1, sticky="e")
        bar.columnconfigure(0, weight=1)
        # Long messages wrap at the width of the window instead of widening it.
        bar.bind("<Configure>", lambda event: status_label.configure(
            wraplength=max(100, event.width - self.progress_bar.winfo_reqwidth() - 12)))
        # The bar keeps the tallest height it has needed. A shorter message, such as
        # "Searching..." after a two-line summary, would otherwise move the buttons and the table
        # while the search keeps the window busy, and their old image would stay on screen.
        status_label.bind("<Configure>", lambda event: bar.rowconfigure(
            0, minsize=max(event.height, int(bar.grid_rowconfigure(0)["minsize"]))))

        self.rowconfigure(1, weight=1)
        self.columnconfigure(0, weight=1)

    # -- subclass hooks --------------------------------------------------------------------------

    def _build_inputs(self, parent):
        """Grid the input frames into row 0 of `parent`."""
        raise NotImplementedError

    def _read_inputs(self):
        """Search parameters; raise ValueError with a message for the user."""
        raise NotImplementedError

    def _search(self, inputs, cancel, progress):
        """Run the search (worker thread, no Tk calls) and return its outcome."""
        raise NotImplementedError

    def _present(self, outcome):
        """(table model, status text) for a finished search."""
        raise NotImplementedError

    def apply_colors(self, colors):
        """Recolour the classic Tk widgets of the tab with a ThemeManager colour set."""
        self.table.apply_colors(colors)

    # -- status ----------------------------------------------------------------------------------

    def set_status(self, text):
        """Persistent status: search state or result summary."""
        self._summary = text
        self._show_status(text)

    def flash_status(self, text, duration_ms=3000):
        """Temporary message (e.g. after a copy), then the summary comes back."""
        self._show_status(text)
        self._flash_job = self.after(duration_ms, lambda: self._show_status(self._summary))

    def _show_status(self, text):
        if self._flash_job is not None:
            self.after_cancel(self._flash_job)
            self._flash_job = None
        self.status_var.set(text)

    # -- search ----------------------------------------------------------------------------------

    def start_search(self, event=None):
        if self._worker is not None:
            return
        try:
            inputs = self._read_inputs()
        except ValueError as error:
            show_error(self, "Invalid input", str(error))
            return
        self.table.set_model(None)      # also removes the sort arrow
        self._cancel = threading.Event()
        self._progress = SearchProgress()
        self._outcome = self._error = None
        self.progress_bar.configure(maximum=1, value=0)
        self.search_button.state(["disabled"])
        self.cancel_button.state(["!disabled"])
        self.set_status(self._progress.phase)
        self._worker = threading.Thread(target=self._worker_main, daemon=True,
                                        args=(inputs, self._cancel, self._progress))
        self._worker.start()
        self.after(self.POLL_MS, self._poll_search)

    def cancel_search(self):
        if self._worker is not None:
            self._cancel.set()
            self.set_status("Cancelling...")

    def _worker_main(self, inputs, cancel, progress):
        try:
            self._outcome = self._search(inputs, cancel, progress)
        except Exception as error:      # reported by _poll_search on the UI thread
            self._error = error

    def _poll_search(self):
        progress = self._progress
        self.progress_bar.configure(maximum=max(progress.total, 1), value=progress.done)
        if self._worker.is_alive():
            if not self._cancel.is_set() and self._summary != progress.phase:
                self.set_status(progress.phase)
            self.after(self.POLL_MS, self._poll_search)
            return
        self._worker = None
        self.search_button.state(["!disabled"])
        self.cancel_button.state(["disabled"])
        if self._error is not None:
            self.set_status("Search failed")
            show_error(self, "Search failed", f"{type(self._error).__name__}: {self._error}")
            return
        model, text = self._present(self._outcome)
        self._outcome = None
        self.table.set_model(model)
        self.set_status(text)


class GeneratorTab(SearchTab):
    COLUMNS = GeneratorResults.COLUMNS
    SEARCH_LABEL = "Generate"

    def _build_inputs(self, parent):
        settings = ttk.LabelFrame(parent, text="Settings", padding=(10, 6))
        settings.grid(row=0, column=0, sticky="nsew")
        settings.columnconfigure(1, weight=1)
        self.seed_var = tk.StringVar()
        self.min_advances_var = tk.StringVar(value="0")
        self.max_advances_var = tk.StringVar(value=str(DEFAULT_MAX_ADVANCES))
        fields = (("Initial Seed", self.seed_var, "seed"),
                  ("Min Advances", self.min_advances_var, "advances"),
                  ("Max Advances", self.max_advances_var, "advances"))
        for row, (label, variable, kind) in enumerate(fields):
            ttk.Label(settings, text=label).grid(row=row, column=0, sticky="w", padx=(0, 8), pady=4)
            entry = input_field(settings, variable, kind, self.start_search)
            entry.grid(row=row, column=1, sticky="ew", pady=4)
            if row == 0:
                entry.focus_set()
        self.trade_offset = TradeOffsetOption(settings, len(fields), 0, self.start_search)
        self.iv_frame = IvRangeFrame(parent, on_submit=self.start_search,
                                     on_message=self.flash_status)
        self.iv_frame.grid(row=0, column=1, sticky="nsew", padx=(8, 0))

    def apply_colors(self, colors):
        super().apply_colors(colors)
        self.trade_offset.apply_colors(colors)
        self.iv_frame.apply_colors(colors)

    def _read_inputs(self):
        seed = parse_seed(self.seed_var.get())
        min_advances = parse_number(self.min_advances_var.get(), "Min Advances", 0, MASK32)
        max_advances = parse_number(self.max_advances_var.get(), "Max Advances", 0, MASK32)
        if min_advances > max_advances:
            raise ValueError(f"Min Advances ({min_advances}) is greater than Max Advances "
                             f"({max_advances}).")
        inputs = (seed, min_advances, max_advances, self.iv_frame.ranges(),
                  self.trade_offset.offset())
        self.seed_var.set(f"{seed:08X}")    # 8 digits without 0x: what the field is sized for
        return inputs

    def _search(self, inputs, cancel, progress):
        seed, min_advances, max_advances, iv_ranges, offset = inputs
        return search_ivs(seed, min_advances, max_advances, iv_ranges, cancel, progress,
                          offset=offset)

    def _present(self, outcome):
        found = plural(len(outcome.seeds), "result")
        if outcome.status == "cancelled":
            if outcome.scanned is None:
                text = f"Search cancelled: {found} found so far"
            else:
                text = f"Search cancelled after {plural(outcome.scanned, 'advance')}: {found}"
        elif outcome.status == "limit":
            text = (f"Stopped at advance {outcome.first + outcome.scanned - 1:,}: reached the "
                    f"limit of {MAX_RESULTS:,} results. Narrow the IV filters or the advances.")
        else:
            text = found
        return GeneratorResults(outcome), text


class SearcherTab(SearchTab):
    COLUMNS = SearcherResults.COLUMNS

    def _build_inputs(self, parent):
        self.iv_frame = IvRangeFrame(parent, on_submit=self.start_search,
                                     on_message=self.flash_status)
        self.iv_frame.grid(row=0, column=0, sticky="nsew")

    def apply_colors(self, colors):
        super().apply_colors(colors)
        self.iv_frame.apply_colors(colors)

    def _read_inputs(self):
        iv_ranges = self.iv_frame.ranges()
        estimate = estimate_seed_count(iv_ranges)
        if estimate > MAX_RESULTS:
            raise ValueError(f"These IV ranges match about {estimate:,} seeds, more than the "
                             f"{MAX_RESULTS:,} that can be listed. Narrow the ranges.")
        return iv_ranges

    def _search(self, iv_ranges, cancel, progress):
        return search_spreads(iv_ranges, cancel, progress)

    def _present(self, outcome):
        found = plural(len(outcome.seeds), "result")
        if outcome.status == "cancelled":
            text = f"Search cancelled: {found} found so far"
        elif outcome.status == "limit":
            text = (f"Stopped at the limit of {MAX_RESULTS:,} results: the list is incomplete. "
                    "Narrow the IV ranges.")
        else:
            text = found
        return SearcherResults(outcome), text


class SeedRtcTab(SearchTab):
    COLUMNS = RtcResults.COLUMNS

    def __init__(self, master, settings):
        self._settings = settings
        super().__init__(master)

    def _build_inputs(self, parent):
        settings = ttk.LabelFrame(parent, text="Settings", padding=(10, 6))
        settings.grid(row=0, column=0, sticky="nsew")
        settings.columnconfigure((1, 3), weight=1)
        self.origin_var = tk.StringVar(value=f"{self._settings.origin_seed:08X}")
        self.target_var = tk.StringVar()
        self.rtc_var = tk.StringVar(value=rtc_text(0))
        self.min_advances_var = tk.StringVar(value=str(DEFAULT_MIN_ADVANCES))
        self.max_advances_var = tk.StringVar(value=str(DEFAULT_MAX_ADVANCES))
        self.max_results_var = tk.StringVar(value=str(DEFAULT_RTC_MAX_RESULTS))
        fields = (("Origin Seed", self.origin_var, "seed", 0, 0),
                  ("Target Seed", self.target_var, "seed", 1, 0),
                  ("Initial RTC", self.rtc_var, "rtc", 2, 0),
                  ("Min Advances", self.min_advances_var, "advances", 0, 2),
                  ("Max Advances", self.max_advances_var, "advances", 1, 2),
                  ("Max Results", self.max_results_var, "results", 2, 2))
        for label, variable, kind, row, column in fields:
            ttk.Label(settings, text=label).grid(row=row, column=column, sticky="w", pady=4,
                                                 padx=(16 if column else 0, 8))
            # Fields in the same column stretch to the widest one, so the edges line up.
            entry = input_field(settings, variable, kind, self.start_search)
            entry.grid(row=row, column=column + 1, sticky="ew", pady=4)
            if kind == "rtc":
                entry.bind("<FocusOut>", self._finish_rtc)
        # The boot seed follows the RTC this way only in Dolphin: the note sits under the RTC,
        # the Trade Offset under the advances.
        ttk.Label(settings, text="Emulator only", style="Note.TLabel").grid(
            row=3, column=0, columnspan=2, sticky="w", pady=(2, 0))
        self.trade_offset = TradeOffsetOption(settings, 3, 2, self.start_search)
        self._last_rtc = self.rtc_var.get()     # put back when a left field has no date

    def apply_colors(self, colors):
        super().apply_colors(colors)
        self.trade_offset.apply_colors(colors)

    def _finish_rtc(self, event=None):
        """A left Initial RTC field always shows a whole date and time."""
        text = finish_rtc(self.rtc_var.get()) or self._last_rtc
        self.rtc_var.set(text)
        self._last_rtc = text

    def _read_inputs(self):
        origin = parse_seed(self.origin_var.get(), "Origin Seed")
        target = parse_seed(self.target_var.get(), "Target Seed")
        self._finish_rtc()
        first_second = parse_rtc(self.rtc_var.get(), "Initial RTC")
        min_advances = parse_number(self.min_advances_var.get(), "Min Advances", 0, MASK32)
        max_advances = parse_number(self.max_advances_var.get(), "Max Advances", 0, MASK32)
        if min_advances > max_advances:
            raise ValueError(f"Min Advances ({min_advances}) is greater than Max Advances "
                             f"({max_advances}).")
        max_results = parse_number(self.max_results_var.get(), "Max Results", 1, MAX_RESULTS)
        offset = self.trade_offset.offset()
        # Show the seeds as they were understood: 8 digits (the date is already complete).
        self.origin_var.set(f"{origin:08X}")
        self.target_var.set(f"{target:08X}")
        self._settings.origin_seed = origin
        return origin, target, first_second, min_advances, max_advances, max_results, offset

    def _search(self, inputs, cancel, progress):
        *arguments, offset = inputs
        return search_rtc(*arguments, cancel=cancel, progress=progress, offset=offset)

    def _present(self, outcome):
        found = plural(len(outcome.seconds), "result")
        if outcome.status == "cancelled":
            text = f"Search cancelled: {found} found so far"
        elif outcome.status == "limit":
            text = f"{found}: Max Results reached at {rtc_text(outcome.seconds[-1])}"
        else:
            text = f"{found} up to {rtc_text(RTC_LAST_SECOND)}"
        return RtcResults(outcome), text

    def remember_origin_seed(self):
        """Store the Origin Seed in the settings file if the field holds a valid value."""
        try:
            self._settings.origin_seed = parse_seed(self.origin_var.get(), "Origin Seed")
        except ValueError:
            pass


class ObservationTab(SearchTab):
    """The seed from a sequence of things the game shows: Settings, one button per thing that can
    be seen, and the list of the entries made so far, with Remove and Clear.

    Subclasses define CHOICES as (button text, list text, code) and implement the search hooks;
    self.codes holds the codes of the entries in order.
    """

    CHOICES = ()
    CHOICES_TITLE = ""
    CHOICE_COLUMNS = 1
    CHOICE_ROWS_STRETCH = False         # True: the buttons also share the height of their box
    DEFAULT_MAX_ADVANCES = DEFAULT_MAX_ADVANCES

    def __init__(self, master):
        self.codes = []
        self._list_names = {code: name for _, name, code in self.CHOICES}
        super().__init__(master)

    def _build_inputs(self, parent):
        settings = ttk.LabelFrame(parent, text="Settings", padding=(10, 6))
        settings.grid(row=0, column=0, sticky="nsew")
        settings.columnconfigure(1, weight=1)
        self.seed_var = tk.StringVar()
        self.min_advances_var = tk.StringVar(value="0")
        self.max_advances_var = tk.StringVar(value=str(self.DEFAULT_MAX_ADVANCES))
        self.setting_fields = []
        fields = (("Initial Seed", self.seed_var, "seed"),
                  ("Min Advances", self.min_advances_var, "advances"),
                  ("Max Advances", self.max_advances_var, "advances"))
        for row, (label, variable, kind) in enumerate(fields):
            ttk.Label(settings, text=label).grid(row=row, column=0, sticky="w", padx=(0, 8), pady=4)
            field = input_field(settings, variable, kind, self.start_search)
            field.grid(row=row, column=1, sticky="ew", pady=4)
            self.setting_fields.append(field)
        self._build_options(settings, 3)

        choices = ttk.LabelFrame(parent, text=self.CHOICES_TITLE, padding=(6, 6))
        choices.grid(row=0, column=1, sticky="nsew", padx=(8, 0))
        choices.columnconfigure(tuple(range(self.CHOICE_COLUMNS)), weight=1)
        if self.CHOICE_ROWS_STRETCH:
            rows = -(-len(self.CHOICES) // self.CHOICE_COLUMNS)
            choices.rowconfigure(tuple(range(rows)), weight=1)
        self.choice_buttons = []
        for index, (text, _, code) in enumerate(self.CHOICES):
            image = self._choice_image(code)
            # A button with an image shows only the image; its text is kept for reference.
            looks = {} if image is None else {"image": image, "compound": "image"}
            button = ttk.Button(choices, text=text, width=self._choice_width(), **looks,
                                command=lambda code=code: self.add_entry(code))
            button.grid(row=index // self.CHOICE_COLUMNS, column=index % self.CHOICE_COLUMNS,
                        sticky="nsew", padx=2, pady=2)
            self.choice_buttons.append(button)

        entries = ttk.LabelFrame(parent, text="Entries", padding=(10, 6))
        entries.grid(row=0, column=2, sticky="nsew", padx=(8, 0))
        names = [f"99. {name}" for name in self._list_width_names()]
        # A few lines: the list stretches to the height of the frames beside it.
        self.entry_list = tk.Listbox(entries, height=3, width=text_width(names),
                                     selectmode="extended", activestyle="none",
                                     exportselection=False, font="TkDefaultFont", borderwidth=0,
                                     highlightthickness=1, relief="flat")
        scrollbar = ttk.Scrollbar(entries, orient="vertical", command=self.entry_list.yview)
        self.entry_list.configure(yscrollcommand=scrollbar.set)
        self.entry_list.grid(row=0, column=0, columnspan=2, sticky="nsew")
        scrollbar.grid(row=0, column=2, sticky="ns")
        for sequence in ("<Delete>", "<BackSpace>"):
            self.entry_list.bind(sequence, self.remove_entries)
        ttk.Button(entries, text="Remove", width=7, command=self.remove_entries).grid(
            row=1, column=0, sticky="ew", pady=(6, 0), padx=(0, 3))
        ttk.Button(entries, text="Clear", width=7, command=self.clear_entries).grid(
            row=1, column=1, columnspan=2, sticky="ew", pady=(6, 0), padx=(3, 0))
        entries.rowconfigure(0, weight=1)
        entries.columnconfigure((0, 1), weight=1)

    def _build_options(self, settings, row):
        """Extra widgets under the Settings fields, from grid row `row`."""

    def _choice_width(self):
        """`width` of the choice buttons. -1 (at least one character): as wide as their text
        instead of the theme's 11 characters; the grid lines them up."""
        return -1

    def _choice_image(self, code):
        """Image shown on the button of `code` instead of its text, or None."""
        return None

    def _list_width_names(self):
        """Names the entry list must fit."""
        return [name for _, name, _ in self.CHOICES]

    # -- entries ---------------------------------------------------------------------------------

    def add_entry(self, code):
        self.codes.append(code)
        self.entry_list.insert("end", self._entry_text(len(self.codes), code))
        self.entry_list.selection_clear(0, "end")
        self.entry_list.see("end")

    def remove_entries(self, event=None):
        """Remove the selected entries, or the last one when none is selected."""
        selected = self.entry_list.curselection()
        if not selected and self.codes:
            selected = (len(self.codes) - 1,)
        for index in sorted(selected, reverse=True):
            del self.codes[index]
        if selected:
            self._show_entries()
        return "break"

    def clear_entries(self):
        self.codes.clear()
        self._show_entries()

    def _show_entries(self):
        self.entry_list.delete(0, "end")
        for number, code in enumerate(self.codes, start=1):
            self.entry_list.insert("end", self._entry_text(number, code))
        self.entry_list.see("end")

    def _entry_text(self, number, code):
        return f"{number}. {self._list_names[code]}"

    def apply_colors(self, colors):
        super().apply_colors(colors)
        self.entry_list.configure(background=colors["list_background"],
                                  foreground=colors["list_text"],
                                  selectbackground=colors["list_selected"],
                                  selectforeground=colors["list_selected_text"],
                                  highlightbackground=colors["list_border"],
                                  highlightcolor=colors["list_focus"],
                                  disabledforeground=colors["list_disabled_text"])

    # -- inputs ----------------------------------------------------------------------------------

    def _read_range(self, span, what):
        """(Initial Seed, Min Advances, Max Advances); `span` advances are taken by the entries."""
        seed = parse_seed(self.seed_var.get())
        min_advances = parse_number(self.min_advances_var.get(), "Min Advances", 0, MASK32)
        max_advances = parse_number(self.max_advances_var.get(), "Max Advances", 0, MASK32)
        if min_advances > max_advances:
            raise ValueError(f"Min Advances ({min_advances}) is greater than Max Advances "
                             f"({max_advances}).")
        if max_advances < span:
            raise ValueError(f"Max Advances must be at least {span:,}: the advances taken by "
                             f"the {what}.")
        self.seed_var.set(f"{seed:08X}")    # 8 digits without 0x: what the field is sized for
        return seed, min_advances, max_advances

    def _summary_text(self, outcome):
        found = plural(len(outcome.seeds), "result")
        if outcome.status == "cancelled":
            return f"Search cancelled: {found} found so far"
        if outcome.status == "limit":
            return (f"Stopped at the limit of {OBSERVATION_MAX_RESULTS:,} results: enter more "
                    "entries or narrow the advances.")
        return found


class BruteforceTab(ObservationTab):
    """An ObservationTab that can also try every state: a Bruteforce check box under the Settings
    fields, with an optional NOTE on its right."""

    NOTE = None

    def _build_options(self, settings, row):
        self.bruteforce_var = tk.BooleanVar(value=False)
        options = ttk.Frame(settings)       # its own frame: the field columns keep their widths
        options.grid(row=row, column=0, columnspan=2, sticky="ew", pady=(6, 0))
        ttk.Checkbutton(options, text="Bruteforce", variable=self.bruteforce_var,
                        command=self._on_bruteforce).pack(side="left")
        if self.NOTE:
            ttk.Label(options, text=self.NOTE, style="Note.TLabel").pack(side="right")

    def _on_bruteforce(self):
        """A bruteforce search has no Initial Seed and no advances."""
        state = ["disabled"] if self.bruteforce_var.get() else ["!disabled"]
        for field in self.setting_fields:
            field.state(state)


class CameraTab(BruteforceTab):
    COLUMNS = CameraResults.COLUMNS
    # Two columns, each movement next to its "Up +" variant; the long labels share a column.
    CHOICES = tuple((CAMERA_MOVES[code], CAMERA_MOVES[code], code)
                    for code in (0, 6, 2, 5, 3, 4, 1)) + ((NOT_CLEAR, NOT_CLEAR, NOT_CLEAR_CODE),)
    CHOICES_TITLE = "Camera"
    CHOICE_COLUMNS = 2

    def _read_inputs(self):
        codes = list(self.codes)
        if not codes:
            raise ValueError("Enter the camera movements you saw, in order, with the buttons.")
        known = sum(code >= 0 for code in codes)
        if self.bruteforce_var.get():
            if known < BRUTEFORCE_MIN_CAMERAS:
                raise ValueError(f"Bruteforce needs at least {BRUTEFORCE_MIN_CAMERAS} camera "
                                 f"movements other than {NOT_CLEAR} ({known} entered).")
            return None, 0, 0, codes, True
        if not known:
            raise ValueError(f"Enter at least one camera movement other than {NOT_CLEAR}.")
        what = f"{plural(len(codes), 'camera')} ({CALLS_PER_CAMERA} each)"
        seed, min_advances, max_advances = self._read_range(CALLS_PER_CAMERA * len(codes), what)
        return seed, min_advances, max_advances, codes, False

    def _search(self, inputs, cancel, progress):
        seed, min_advances, max_advances, codes, bruteforce = inputs
        return search_camera(seed, min_advances, max_advances, codes, bruteforce, cancel, progress)

    def _present(self, outcome):
        return CameraResults(outcome), self._summary_text(outcome)


class DexTab(ObservationTab):
    """The version radio buttons (JPN Pt, GER) choose how the game draws the description: the two
    buttons show that version's texts, and every version keeps its own entries."""

    COLUMNS = DexResults.COLUMNS
    CHOICES = tuple((DEX_VERSIONS[DEFAULT_DEX_VERSION].buttons[code],
                     DEX_VERSIONS[DEFAULT_DEX_VERSION].list_names[code], code) for code in (0, 1))
    CHOICES_TITLE = "Description"
    DEFAULT_MAX_ADVANCES = DEFAULT_DEX_MAX_ADVANCES

    def __init__(self, master):
        self.version = DEFAULT_DEX_VERSION
        self._other_entries = {}            # entries of the versions not shown, by version
        super().__init__(master)

    def _build_options(self, settings, row):
        self.version_var = tk.StringVar(value=self.version)
        versions = ttk.Frame(settings)
        versions.grid(row=row, column=0, columnspan=2, sticky="w", pady=(6, 0))
        for column, name in enumerate(DEX_VERSIONS):
            ttk.Radiobutton(versions, text=name, value=name, variable=self.version_var,
                            command=self._on_version).grid(row=0, column=column, padx=(0, 12))

    def _choice_width(self):
        # Wide enough for the texts of every version: switching does not move the layout.
        return text_width([line for dex in DEX_VERSIONS.values() for text in dex.buttons
                           for line in text.split("\n")], margin=0)

    def _list_width_names(self):
        return [name for dex in DEX_VERSIONS.values() for name in dex.list_names]

    def _on_version(self):
        version = self.version_var.get()
        if version == self.version:
            return
        self._other_entries[self.version] = self.codes
        self.codes = self._other_entries.pop(version, [])
        self.version = version
        dex = DEX_VERSIONS[version]
        for code, button in enumerate(self.choice_buttons):
            button.configure(text=dex.buttons[code])
        self._list_names = dict(enumerate(dex.list_names))
        self._show_entries()

    def _read_inputs(self):
        codes = list(self.codes)
        if not codes:
            raise ValueError("Enter the Pokédex descriptions you saw, in order, with the buttons.")
        what = plural(len(codes), "description")
        seed, min_advances, max_advances = self._read_range(len(codes), what)
        return seed, min_advances, max_advances, codes, self.version

    def _search(self, inputs, cancel, progress):
        seed, min_advances, max_advances, codes, version = inputs
        return version, search_dex(seed, min_advances, max_advances, codes, version, cancel,
                                   progress)

    def _present(self, result):
        version, outcome = result
        return DexResults(outcome, version), f"{self._summary_text(outcome)} ({version})"


class DiceTab(BruteforceTab):
    """The faces of dice rolls in a row. Only JPN Platinum has the dice toy."""

    COLUMNS = DiceResults.COLUMNS
    CHOICES = tuple((str(face), f"Face {face}", face) for face in DICE_FACES)
    CHOICES_TITLE = "Dice"
    CHOICE_COLUMNS = 3                  # 1 2 3 / 4 5 6, as large as their box
    CHOICE_ROWS_STRETCH = True
    NOTE = "JPN Pt only"

    def __init__(self, master):
        # The buttons show the faces of a die, in the text colour of the theme.
        self._face_size = round(2.4 * tkfont.nametofont("TkDefaultFont").metrics("linespace"))
        self._face_color = None
        self._face_images = {face: tk.PhotoImage(master=master) for face in DICE_FACES}
        self._draw_faces(DEFAULT_TABLE_COLORS["table_text"])
        super().__init__(master)

    def _choice_image(self, face):
        return self._face_images[face]

    def _draw_faces(self, color):
        if color != self._face_color:
            self._face_color = color
            for face, image in self._face_images.items():
                image.configure(data=die_face_png(face, self._face_size, color))

    def apply_colors(self, colors):
        super().apply_colors(colors)
        self._draw_faces(colors["text"])

    def _read_inputs(self):
        faces = list(self.codes)
        if not faces:
            raise ValueError("Enter the faces of the dice rolls you saw, in order, with the "
                             "buttons.")
        if self.bruteforce_var.get():
            if len(faces) < BRUTEFORCE_MIN_ROLLS:
                raise ValueError(f"Bruteforce needs at least {BRUTEFORCE_MIN_ROLLS} dice rolls "
                                 f"({len(faces)} entered).")
            return None, 0, 0, faces, True
        span = sum(roll_calls(face) for face in faces)
        what = f"{plural(len(faces), 'roll')} (3 calls each, 5 for a 1, 5 or 6)"
        seed, min_advances, max_advances = self._read_range(span, what)
        return seed, min_advances, max_advances, faces, False

    def _search(self, inputs, cancel, progress):
        seed, min_advances, max_advances, faces, bruteforce = inputs
        return search_dice(seed, min_advances, max_advances, faces, bruteforce, cancel, progress)

    def _present(self, outcome):
        return DiceResults(outcome), self._summary_text(outcome)


# ------------------------------------------------------------------------------------------------
# Themes
# ------------------------------------------------------------------------------------------------

# Both themes are drawn by ttk's "clam" theme with the same sizes: switching changes colours only.
PALETTES = {
    "Light": {
        "background": "#F0F0F0",    # window, frames, labels
        "surface": "#FFFFFF",       # entry fields, table body, menus
        "raised": "#E1E1E1",        # buttons, inactive tabs, spinbox arrows
        "hover": "#E5F1FB",
        "pressed": "#CCE4F7",
        "border": "#ADADAD",        # entry fields, buttons, frames
        "frame": "#828790",         # around the tables
        "grid": "#D5D5D5",          # between table cells
        "heading": "#FFFFFF", "heading_hover": "#D9EBF9", "heading_pressed": "#BCDCF4",
        "trough": "#F0F0F0", "thumb": "#C8C8C8", "thumb_active": "#A6A6A6",
        "text": "#000000",
        "muted": "#8C8C8C",         # disabled text
        "accent": "#0078D7",        # selection and focus
        "accent_text": "#FFFFFF",
        "link": "#0066CC",
        "note": "#9A5B00",          # notes such as "Emulator only"
        "progress": "#06B025",
    },
    "Dark": {
        "background": "#202020",
        "surface": "#2B2B2B",
        "raised": "#353535",
        "hover": "#404040",
        "pressed": "#4A4A4A",
        "border": "#505050",
        "frame": "#505050",
        "grid": "#454545",
        "heading": "#353535", "heading_hover": "#404040", "heading_pressed": "#4A4A4A",
        "trough": "#2B2B2B", "thumb": "#4D4D4D", "thumb_active": "#5E5E5E",
        "text": "#E6E6E6",
        "muted": "#8C8C8C",
        "accent": "#2F6BC4",
        "accent_text": "#FFFFFF",
        "link": "#5AA9FF",
        "note": "#E8B04B",
        "progress": "#3C9F4F",
    },
}


def menu_colors(colors):
    """tk.Menu options for a ThemeManager colour set."""
    return {"background": colors["menu_background"], "foreground": colors["menu_text"],
            "activebackground": colors["menu_active_background"],
            "activeforeground": colors["menu_active_text"], "selectcolor": colors["menu_text"],
            # without it Windows draws greyed-out entries embossed, as light as the others in Dark
            "disabledforeground": colors["menu_disabled_text"]}


def set_dark_title_bar(window, dark):
    """Ask Windows 10/11 or macOS for a dark or light title bar (on macOS the native menus follow
    it too); on Linux the window manager draws the title bar and nothing happens."""
    if on_macos(window):
        try:        # Tk 8.6.10 and later
            window.tk.call("::tk::unsupported::MacWindowStyle", "appearance", str(window),
                           "darkaqua" if dark else "aqua")
        except tk.TclError:
            pass
        return
    if sys.platform != "win32":
        return
    try:
        import ctypes
        window.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(window.winfo_id())
        value = ctypes.c_int(1 if dark else 0)
        for attribute in (20, 19):      # DWMWA_USE_IMMERSIVE_DARK_MODE (19 on early Windows 10)
            if ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, attribute, ctypes.byref(value),
                                                          ctypes.sizeof(value)) == 0:
                break
        # SWP_NOSIZE | SWP_NOMOVE | SWP_NOZORDER | SWP_NOACTIVATE | SWP_FRAMECHANGED: redraw now.
        ctypes.windll.user32.SetWindowPos(hwnd, 0, 0, 0, 0, 0, 0x0037)
    except (AttributeError, OSError):
        pass


class ThemeManager:
    """Applies a palette of PALETTES to the whole application.

    Both themes use ttk's "clam" theme with identical sizes and paddings, so switching only
    changes colours. ttk widgets get them through their styles; the classic Tk widgets (table
    Canvases, menus, the Options button) through the listeners, which receive a colour set.
    """

    def __init__(self, root):
        self.root = root
        self.style = ttk.Style(root)
        self.name = None
        self.colors = {}
        self._listeners = []
        self.note_font = tkfont.nametofont("TkDefaultFont").copy()      # "Note.TLabel"
        self.note_font.configure(slant="italic")
        self._check_images = None       # the check box images, made by the first apply()

    def add_listener(self, callback):
        """callback(colors) runs at every theme change."""
        self._listeners.append(callback)

    def apply(self, name):
        palette = PALETTES[name]
        self.style.theme_use("clam")
        self._configure_styles(palette)
        self.name, self.colors = name, self._widget_colors(palette)
        self.root.configure(background=palette["background"])
        for callback in self._listeners:
            callback(self.colors)
        set_dark_title_bar(self.root, name == "Dark")

    @staticmethod
    def _widget_colors(p):
        """The colour set the listeners receive, for the palette `p`."""
        return {
            "background": p["background"], "text": p["text"],
            "table_background": p["surface"], "table_text": p["text"],
            "table_selected": p["accent"], "table_selected_text": p["accent_text"],
            "table_border": p["frame"], "table_grid": p["grid"],
            "heading_background": p["heading"], "heading_hover": p["heading_hover"],
            "heading_pressed": p["heading_pressed"], "heading_text": p["text"],
            "menu_background": p["surface"], "menu_text": p["text"],
            "menu_active_background": p["accent"], "menu_active_text": p["accent_text"],
            "menu_disabled_text": p["muted"],
            "bar_background": p["background"], "bar_text": p["text"],
            "bar_active_background": p["hover"],
            "link": p["link"],
            "list_background": p["surface"], "list_text": p["text"],
            "list_selected": p["accent"], "list_selected_text": p["accent_text"],
            "list_border": p["border"], "list_focus": p["accent"], "list_disabled_text": p["muted"],
        }

    def _configure_styles(self, p):
        style = self.style
        flat = {"lightcolor": p["raised"], "darkcolor": p["raised"]}
        style.configure(".", background=p["background"], foreground=p["text"],
                        fieldbackground=p["surface"], bordercolor=p["border"],
                        troughcolor=p["trough"], selectbackground=p["accent"],
                        selectforeground=p["accent_text"], insertcolor=p["text"],
                        arrowcolor=p["text"], focuscolor=p["accent"], **flat)
        # clam's own hover colour is a fixed light grey: use the palette's instead.
        style.map(".", background=[("disabled", p["background"]), ("active", p["hover"])],
                  foreground=[("disabled", p["muted"])],
                  selectbackground=[("!focus", p["raised"])],
                  selectforeground=[("!focus", p["text"])])
        style.configure("TFrame", background=p["background"])
        style.configure("TLabel", background=p["background"], foreground=p["text"])
        # The body of a message (MessageDialog), on the surface colour like Windows shows it.
        style.configure("Dialog.TFrame", background=p["surface"])
        style.configure("Dialog.TLabel", background=p["surface"], foreground=p["text"])
        style.configure("Note.TLabel", foreground=p["note"], font=self.note_font)
        style.configure("TLabelframe", background=p["background"], bordercolor=p["border"],
                        lightcolor=p["background"], darkcolor=p["background"])
        style.configure("TLabelframe.Label", background=p["background"], foreground=p["text"])
        pressed_or_hover = [("pressed", p["pressed"]), ("active", p["hover"])]
        style.configure("TButton", background=p["raised"], foreground=p["text"],
                        bordercolor=p["border"], focuscolor=p["accent"], justify="center", **flat)
        style.map("TButton", background=[("disabled", p["background"])] + pressed_or_hover,
                  foreground=[("disabled", p["muted"])], bordercolor=[("disabled", p["raised"])],
                  lightcolor=pressed_or_hover, darkcolor=pressed_or_hover)
        for name in ("TEntry", "TSpinbox"):
            style.configure(name, fieldbackground=p["surface"], foreground=p["text"],
                            background=p["raised"], insertcolor=p["text"], arrowcolor=p["text"],
                            bordercolor=p["border"], lightcolor=p["surface"],
                            darkcolor=p["surface"])
            style.map(name, bordercolor=[("focus", p["accent"])],
                      lightcolor=[("focus", p["surface"])], darkcolor=[("focus", p["surface"])],
                      background=[("active", p["hover"])], arrowcolor=[("disabled", p["muted"])],
                      fieldbackground=[("disabled", p["background"])],
                      foreground=[("disabled", p["muted"])])
        # The Trade Offset drop-down is read-only: its field looks like an entry, without the
        # selection colour that clam gives a focused read-only field.
        style.configure("TCombobox", fieldbackground=p["surface"], foreground=p["text"],
                        background=p["raised"], arrowcolor=p["text"], bordercolor=p["border"],
                        lightcolor=p["surface"], darkcolor=p["surface"],
                        selectbackground=p["surface"], selectforeground=p["text"])
        style.map("TCombobox",
                  fieldbackground=[("disabled", p["background"]), ("readonly", p["surface"])],
                  foreground=[("disabled", p["muted"]), ("readonly", p["text"])],
                  background=[("disabled", p["background"]), ("pressed", p["pressed"]),
                              ("active", p["hover"])],
                  arrowcolor=[("disabled", p["muted"])], bordercolor=[("focus", p["accent"])],
                  lightcolor=[("focus", p["surface"])], darkcolor=[("focus", p["surface"])],
                  selectbackground=[("readonly", p["surface"])],
                  selectforeground=[("readonly", p["text"])])
        style.configure("ComboboxPopdownFrame", background=p["surface"], bordercolor=p["border"],
                        lightcolor=p["surface"], darkcolor=p["surface"])
        # Its list is a classic Listbox that Tk creates when it first opens: it reads its colours
        # from the option database.
        for option, color in (("background", p["surface"]), ("foreground", p["text"]),
                              ("selectBackground", p["accent"]),
                              ("selectForeground", p["accent_text"])):
            self.root.option_add(f"*TCombobox*Listbox.{option}", color)
        # The Options button on macOS (a ttk Menubutton there): flat and on the window colour like
        # the classic one elsewhere, as wide as its text, without the drop-down arrow.
        style.layout("Options.TMenubutton", [("Menubutton.border", {"sticky": "nswe", "children": [
            ("Menubutton.padding", {"sticky": "nswe", "children": [
                ("Menubutton.label", {"sticky": ""})]})]})])
        style.configure("Options.TMenubutton", background=p["background"], foreground=p["text"],
                        bordercolor=p["background"], lightcolor=p["background"],
                        darkcolor=p["background"], relief="flat", padding=(6, 1), width=0)
        hover = [("pressed", p["hover"]), ("active", p["hover"])]
        style.map("Options.TMenubutton", background=hover, bordercolor=hover, lightcolor=hover,
                  darkcolor=hover)
        # Check boxes and radio buttons keep the window colour on hover: only the indicator reacts.
        for name in ("TCheckbutton", "TRadiobutton"):
            style.configure(name, background=p["background"], foreground=p["text"],
                            indicatorbackground=p["surface"], indicatorforeground=p["text"],
                            upperbordercolor=p["border"], lowerbordercolor=p["border"])
            style.map(name, background=[("active", p["background"])],
                      foreground=[("disabled", p["muted"])],
                      indicatorbackground=[("pressed", p["pressed"]), ("active", p["hover"]),
                                           ("disabled", p["background"])])
        self._configure_check_boxes(p)
        style.configure("TNotebook", background=p["background"], bordercolor=p["border"],
                        lightcolor=p["background"], darkcolor=p["background"])
        style.configure("TNotebook.Tab", background=p["raised"], foreground=p["text"],
                        bordercolor=p["border"], **flat)
        tab_states = [("selected", p["background"]), ("active", p["hover"])]
        style.map("TNotebook.Tab", background=tab_states, lightcolor=tab_states,
                  darkcolor=tab_states)
        thumb_states = [("pressed", p["thumb_active"]), ("active", p["thumb_active"])]
        style.configure("Vertical.TScrollbar", background=p["thumb"], troughcolor=p["trough"],
                        bordercolor=p["border"], arrowcolor=p["text"], gripcount=0,
                        lightcolor=p["thumb"], darkcolor=p["thumb"])
        style.map("Vertical.TScrollbar", background=thumb_states, lightcolor=thumb_states,
                  darkcolor=thumb_states, arrowcolor=[("disabled", p["muted"])])
        style.configure("Horizontal.TProgressbar", background=p["progress"],
                        troughcolor=p["surface"], bordercolor=p["border"],
                        lightcolor=p["progress"], darkcolor=p["progress"])

    def _configure_check_boxes(self, p):
        """Check boxes show a check mark (✓) where clam draws a cross: their indicator is an image
        element with one image per state, redrawn in the colours of the palette `p`. The box
        follows the font size and keeps clam's margins around it (1 pixel, 4 on the right)."""
        line = tkfont.nametofont("TkDefaultFont").metrics("linespace")
        size = max(10, round(0.8 * line))
        margins = (1, 1, max(4, round(line / 4)), 1)
        looks = {                       # image: (fill, mark), the border is always p["border"]
            "off": (p["surface"], None), "on": (p["surface"], p["text"]),
            "off_active": (p["hover"], None), "on_active": (p["hover"], p["text"]),
            "off_pressed": (p["pressed"], None), "on_pressed": (p["pressed"], p["text"]),
            "off_disabled": (p["background"], None), "on_disabled": (p["background"], p["muted"]),
        }
        first = self._check_images is None
        if first:
            self._check_images = {key: tk.PhotoImage(master=self.root) for key in looks}
        images = self._check_images
        for key, (fill, mark) in looks.items():
            images[key].configure(data=check_box_png(size, margins, p["border"], fill, mark))
        if first:                       # the element stays in the clam theme: create it once
            self.style.element_create(
                "Check.indicator", "image", images["off"],
                ("disabled", "selected", images["on_disabled"]),
                ("disabled", images["off_disabled"]),
                ("pressed", "selected", images["on_pressed"]), ("pressed", images["off_pressed"]),
                ("active", "selected", images["on_active"]), ("active", images["off_active"]),
                ("selected", images["on"]), sticky="")
        self.style.layout("TCheckbutton", [("Checkbutton.padding", {"sticky": "nswe", "children": [
            ("Check.indicator", {"side": "left", "sticky": ""}),
            ("Checkbutton.focus", {"side": "left", "sticky": "w", "children": [
                ("Checkbutton.label", {"sticky": "nswe"})]})]})])


def reveal_window(window, dark):
    """Show the withdrawn `window` with its title bar already dark or light: it stays invisible
    until the title bar has the theme's colours, so the bar never flashes in the other colour."""
    window.attributes("-alpha", 0.0)
    window.deiconify()
    set_dark_title_bar(window, dark)
    window.attributes("-alpha", 1.0)


def present_dialog(dialog, master, dark):
    """Show the withdrawn `dialog` centred on `master` (see reveal_window)."""
    dialog.update_idletasks()
    x = master.winfo_rootx() + (master.winfo_width() - dialog.winfo_reqwidth()) // 2
    y = master.winfo_rooty() + (master.winfo_height() - dialog.winfo_reqheight()) // 3
    dialog.geometry(f"+{max(x, 0)}+{max(y, 0)}")
    reveal_window(dialog, dark)


def error_sound(widget):
    """The sound of a Windows error message (the bell elsewhere)."""
    if sys.platform == "win32":
        try:
            import winsound
            winsound.MessageBeep(winsound.MB_ICONHAND)
            return
        except (ImportError, RuntimeError):
            pass
    widget.bell()


class MessageDialog(tk.Toplevel):
    """An error message in the colours of the theme, laid out like the Windows message box (whose
    native window stays light in the dark theme): the red icon and the text on the surface
    colour, OK in a bar below. Return, Escape and Space close it; Ctrl+C copies the message."""

    def __init__(self, master, theme, title, message):
        super().__init__(master)
        self.withdraw()
        self.title(title)
        self.resizable(False, False)
        self.transient(master)
        theme_name = theme.name if theme is not None else "Light"
        self.configure(background=PALETTES[theme_name]["background"])
        line = tkfont.nametofont("TkDefaultFont").metrics("linespace")
        body = ttk.Frame(self, style="Dialog.TFrame",
                         padding=(round(1.5 * line), round(1.4 * line)))
        body.pack(fill="both", expand=True)
        self._icon = tk.PhotoImage(master=self, data=error_icon_png(2 * line))
        ttk.Label(body, image=self._icon, style="Dialog.TLabel").grid(
            row=0, column=0, sticky="n", padx=(0, round(0.75 * line)))
        ttk.Label(body, text=message, style="Dialog.TLabel", justify="left",
                  wraplength=24 * line).grid(row=0, column=1, sticky="w")
        bar = ttk.Frame(self, padding=(round(0.75 * line), round(0.6 * line)))
        bar.pack(fill="x")
        ok_button = ttk.Button(bar, text="OK", command=self.destroy)
        ok_button.pack(side="right")
        for sequence in ("<Return>", "<KP_Enter>", "<Escape>"):
            self.bind(sequence, lambda event: self.destroy())
        for sequence in shortcut_sequences(self, "c"):
            self.bind(sequence, lambda event: self._copy(message))
        present_dialog(self, master, theme_name == "Dark")
        ok_button.focus_set()
        self.grab_set()
        error_sound(self)

    def _copy(self, message):
        self.clipboard_clear()
        self.clipboard_append(message)


def show_error(parent, title, message):
    """Show an error message over the window of `parent` and wait until it is closed, then give
    the focus back. The tests replace this function to collect the messages."""
    root = parent.winfo_toplevel()
    try:
        previous = root.focus_get()
    except KeyError:                    # focus in a widget tkinter does not know
        previous = None
    dialog = MessageDialog(root, getattr(root, "theme", None), title, message)
    root.wait_window(dialog)
    try:
        if previous is not None and previous.winfo_exists():
            previous.focus_set()
    except tk.TclError:                 # the application was closed meanwhile
        pass


class AboutDialog(tk.Toplevel):
    def __init__(self, master, theme):
        super().__init__(master)
        self.withdraw()
        self.title("About")
        self.resizable(False, False)
        self.transient(master)
        colors = theme.colors
        self.configure(background=colors["background"])
        body = ttk.Frame(self, padding=(24, 18))
        body.pack(fill="both", expand=True)
        # A read-only Text, so that the link sits right after "GitHub: " in a centred line.
        author, lead = f"Author: {AUTHOR_NAME}", "GitHub: "
        font = tkfont.nametofont("TkDefaultFont")
        longest = max(font.measure(text) for text in (APP_DESCRIPTION, author, lead + GITHUB_URL))
        message = tk.Text(body, height=5, width=-(-longest // font.measure("0")) + 2, wrap="none",
                          borderwidth=0, highlightthickness=0, takefocus=0, cursor="arrow",
                          font="TkDefaultFont", background=colors["background"],
                          foreground=colors["text"], selectbackground=colors["table_selected"],
                          selectforeground=colors["table_selected_text"])
        message.tag_configure("line", justify="center")
        message.tag_configure("link", foreground=colors["link"], underline=True)
        message.insert("end", f"{APP_DESCRIPTION}\n\n{author}\n\n{lead}", "line")
        message.insert("end", GITHUB_URL, ("line", "link"))
        message.tag_bind("link", "<Enter>", lambda event: message.configure(cursor="hand2"))
        message.tag_bind("link", "<Leave>", lambda event: message.configure(cursor="arrow"))
        message.tag_bind("link", "<Button-1>", lambda event: webbrowser.open(GITHUB_URL))
        message.configure(state="disabled")
        message.pack()
        ok_button = ttk.Button(body, text="OK", command=self.destroy)
        ok_button.pack(pady=(16, 0))
        for sequence in ("<Return>", "<Escape>"):
            self.bind(sequence, lambda event: self.destroy())
        present_dialog(self, master, theme.name == "Dark")
        ok_button.focus_set()
        self.grab_set()


# ------------------------------------------------------------------------------------------------
# Application
# ------------------------------------------------------------------------------------------------

class RanchRngApp(tk.Tk):
    def __init__(self, settings=None):
        super().__init__()
        self.withdraw()                 # shown once its size is known
        self.settings = settings if settings is not None else AppSettings()
        self.title(APP_TITLE)
        # Mew as the icon of this window and of every dialog (APP_ICONS, at the end of this file):
        # Windows and Linux pick the size they need, macOS shows the first one (256 px) in the Dock.
        self._icons = [tk.PhotoImage(master=self, data=data) for data in APP_ICONS.values()]
        self.iconphoto(True, *self._icons)
        self.theme = ThemeManager(self)
        self.theme_var = tk.StringVar(value=self.settings.theme)
        self._about = None
        self._build_menu()
        notebook = ttk.Notebook(self)
        notebook.pack(fill="both", expand=True, padx=8, pady=(2, 8))
        self.generator_tab = GeneratorTab(notebook)
        self.searcher_tab = SearcherTab(notebook)
        self.seed_rtc_tab = SeedRtcTab(notebook, self.settings)
        self.camera_tab = CameraTab(notebook)
        self.dex_tab = DexTab(notebook)
        self.dice_tab = DiceTab(notebook)
        self.tabs = (self.generator_tab, self.searcher_tab, self.seed_rtc_tab, self.camera_tab,
                     self.dex_tab, self.dice_tab)
        for tab, text in zip(self.tabs, ("Generator", "Searcher", "Seed to RTC", "Seed from Camera",
                                         "Seed from Dex", "Seed from Dice")):
            notebook.add(tab, text=text)
        self.searcher_tab.table.add_context_action("Set Seed as Target Seed",
                                                   self._use_as_target_seed)
        for tab in (self.seed_rtc_tab, self.camera_tab, self.dex_tab, self.dice_tab):
            # The first column of these tables is the seed to start the Generator from.
            tab.table.add_context_action(
                "Set as Initial Seed in Generator",
                lambda values, tab=tab: self._use_as_initial_seed(values, tab))
        self.theme.add_listener(self._color_menu)
        for tab in self.tabs:
            self.theme.add_listener(tab.apply_colors)
        self.theme.apply(self.theme_var.get())
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        if on_macos(self):
            # About and Quit (also Command+Q) of the macOS application menu
            self.createcommand("tkAboutDialog", self.show_about)
            self.createcommand("::tk::mac::Quit", self._on_close)
        # The window opens as wide as its widest tab needs, which is also the smallest width it
        # takes. It can be resized from every side and maximized: the input boxes share the
        # extra width, the results tables get the extra width and height.
        self.update_idletasks()
        width = self.winfo_reqwidth()
        self.minsize(width, MIN_WINDOW_HEIGHT)
        self.geometry(f"{width}x{DEFAULT_WINDOW_HEIGHT}")
        self.resizable(True, True)
        reveal_window(self, self.theme.name == "Dark")

    def _build_menu(self):
        """Options drop-down menu. It is an in-window button rather than the Windows menu bar,
        which keeps the system colours and would stay light in the dark theme."""
        bar = ttk.Frame(self)
        bar.pack(fill="x", padx=8, pady=(4, 0))
        if on_macos(self):
            # macOS draws a classic Menubutton itself, ignoring the theme's colours (light grey
            # in the dark theme): a ttk one is drawn by the clam theme like the rest of the window.
            self.options_button = ttk.Menubutton(bar, text="Options", style="Options.TMenubutton",
                                                 takefocus=0)
        else:
            self.options_button = tk.Menubutton(bar, text="Options", relief="flat", borderwidth=0,
                                                padx=8, pady=3, font="TkDefaultFont", takefocus=0)
        self.options_button.pack(side="left")
        self.options_menu = tk.Menu(self.options_button, tearoff=False)
        self.theme_menu = tk.Menu(self.options_menu, tearoff=False)
        for name in THEMES:
            self.theme_menu.add_radiobutton(label=name, value=name, variable=self.theme_var,
                                            command=self._on_theme_selected)
        self.options_menu.add_cascade(label="Theme", menu=self.theme_menu)
        self.options_menu.add_command(label="About", command=self.show_about)
        self.options_button.configure(menu=self.options_menu)

    def _color_menu(self, colors):
        if isinstance(self.options_button, tk.Menubutton):     # the ttk one uses its style
            self.options_button.configure(background=colors["bar_background"],
                                          foreground=colors["bar_text"],
                                          activebackground=colors["bar_active_background"],
                                          activeforeground=colors["bar_text"])
        for menu in (self.options_menu, self.theme_menu):
            menu.configure(**menu_colors(colors))

    def _on_theme_selected(self):
        name = self.theme_var.get()
        self.theme.apply(name)
        self.settings.theme = name

    def show_about(self):
        if self._about is not None and self._about.winfo_exists():
            self._about.lift()
            return
        self._about = AboutDialog(self, self.theme)

    def _use_as_target_seed(self, values):
        """Searcher row -> Target Seed of the Seed to RTC tab."""
        seed = values[SearcherResults.SEED_COLUMN]
        self.seed_rtc_tab.target_var.set(seed)
        self.searcher_tab.flash_status(f"Target Seed in Seed to RTC set to {seed}")

    def _use_as_initial_seed(self, values, source):
        """Seed to RTC or Seed from Camera / Dex / Dice row -> Initial Seed of the Generator."""
        seed = values[0]
        self.generator_tab.seed_var.set(seed)
        source.flash_status(f"Initial Seed in Generator set to {seed}")

    def _on_close(self):
        for tab in self.tabs:
            tab.cancel_search()
        self.seed_rtc_tab.remember_origin_seed()
        self.destroy()


def enable_dpi_awareness():
    """Render sharp text on scaled Windows displays (must run before the Tk window exists)."""
    if sys.platform == "win32":
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except (AttributeError, OSError):
            pass


def set_taskbar_identity():
    """Give the process its own application ID, so that the Windows taskbar shows the window's
    icon instead of the one of python.exe (must run before the Tk window exists)."""
    if sys.platform == "win32":
        try:
            import ctypes
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("Real96.RanchRNGTool")
        except (AttributeError, OSError):
            pass


def main():
    enable_dpi_awareness()
    set_taskbar_identity()
    RanchRngApp().mainloop()


# The application icon: Mew (from Mew.png), as base64 PNGs. The first one, 256 px, is the macOS Dock
# icon (Tk uses only the first image there); the others are the sizes Windows and Linux ask for at
# 100-200 % display scaling (16-24 px in the title bar, 32-64 px in the taskbar and Alt+Tab).
APP_ICONS = {
    256: (
        "iVBORw0KGgoAAAANSUhEUgAAAQAAAAEACAYAAABccqhmAACBj0lEQVR42ux9B6AkVZX2vVXd/fKbN5kc1AUDYYgiYA"
        "JBVMxZTLuGXXXBXVx3l1VX3V9YXQNmXTe5oqCsiihBQEAkDIMwhAEkwwxhYPK8ebFD3f+cWzece+tWdb83b3IV1HR1"
        "V72O95zzne8kzsqto+3Igw89jXN+WBRFDy25Y+n3y29k59iOWXT48YKJQ1qt5Cwhkn+47e5l5+9Kn79SLoHONhD8P4"
        "P9ExHn4rgjjz4dbv8UR9G3ecTx9A3XLr6pubN95s+c/jfdoPSOYYI9/S/fOve+neEzvfyYY3HNH99KkkOSJPlLIcTC"
        "RCRzGeMsSXa9dc1L0e5sO/rQwzbUatVZIPiM8wh2bnZQDL+CL/KRSqXyRbgdv+z314zsqJ/zn884cwA+QzcIxv+DD7"
        "c3fLxXw8OPgRL4I1jK8+ATX/v5b35th/l8Rx2yKO7v7Z3T3d3Nms0mWHmxfyLEGwRIOxwzOE5v4X6z1ToN0N35pQIo"
        "t8z2osOO2NDV1TUrAosv/0Phh+MIlQFLj6Uy4HwxKIQr4U8u+PXvrrx/R/qMn/34mR+Cm4/CslgEH0V+Nvy8IB9GSG"
        "C7Ee7+Dh75yee/8bUHt+fP84rjXnxmV622Hwj+6XGlwlDotcAb4UdFANe2Wi1UEKfdtPTWUgGUW3Y79ogjN/R294AC"
        "iLSgOyiAK2RAHt8Iez2Oo7+D23F45NafXnLxo9vTZ/r83/zd7giHYX8jCMQrYDXMhvdaiTj5jPB5cfMtJuwb4eGfMa"
        "kM2O8++/WvrN/Wn+cNJ52yf61aPXKyUX9/Ja4cBQoLoL2IqNA7gk8+DyqAkbHRJ2658469SwVQbs52+AsOXtjb0/Ng"
        "X2/vQBzFyvKHFAAPKgflNtwPt0+DQH0WuIOV//Pznz2wLT7Lv/ztJ3vg5rmw7M+F2zmwAA7Wy0CiGy38Gt3w9BwVHC"
        "tQiUQHsC2F/TuwX/rP5375ma35ef78LW8/AKD7HiDsn4P3tBvsB8I7g/cp/wXUot8nUV76HFEEzVaTbRod3XDz7Utn"
        "lwqg3JztiIMOOae3t+esgd5+VqnEvmCr+8wITAdKYQSQxI/g9pZKHP8IHhDf+/H/brH3///O/Ht8fxwW+tfgJ98LHn"
        "qLswhSHoNZ2B/JhSFvKQJQApWgQCUOGpDn4P/b4dLFsH8XnuueT3/132b8s7zx5Ffxp9es2n+v3Xb/xNDgIFju5L3w"
        "+v1WwBPP0qfvTej3Tc+Rvd5ogAIY2XDTbbeWCqDcmB8CPAes/1mD/f0MIKYD+VFoUgHXx1FbRBBABz8Bi7v4iadXrr"
        "joist/M1Pv+wuf+IfD0HuB/a9AOg/yf3Jt6fG/VNit1df+P0UAmgdAo59oCO1BaQ0J4CkvgsOr4ejCT3/1S6s3X/BP"
        "ee3eu++xz/rhjV8f6OuvZIU4Sa29EXbvHL3voQM8N1mvs00jIxtuuPWWUgGUG/MjAEYBdNe6UsKP5QizRxLKW2b9aa"
        "4ED48j7l6btFoj1Wp1Bdy/GFyNK+HU0i99/zvDU3mv5/zdP+6mIP574JVeA8cLMz82QSsa9jvcBr43RWxqNJAYoQkI"
        "PnELEqUEUjUgUcGj8MT/DgdL4HjxP33li5OdfI7TXv+mwTlDQ4ePTYy/crCv/3UQttsH3ku/yLghnm9PhT3JnguhA/"
        "xsE5MTbHhkpDUyOvqJpfcs+0apAMrNbMccdsQ5fT09Zw0ODLAeCCdNAepPiSsIIINrQECfAWXwN0gofu4bX90Qen//"
        "+vdnYRx7Pobu4AfdFx46ioWkXlt9G7409/Wxfpxeg39LrawDpXMUAXELqDK4DA6+DE93L9yuPuvf/lVYkvWorgP3f9"
        "as5U8++aaDDjzwRCBc54DQnwB8SSF0z4TzPMtPhb3oHCgatnHTJjY6Nnb2rcvu/HSpAMotJQAPOniwVqleOtDffzwi"
        "AEACVgF0ZOGVWxC5x771d0OLwXMPgTD+5P5HHmYPr1h+zuKlt9a/+Pf/VIWn/BTsH4dLhhxBz/zS3Pj1jo9PoH7kHV"
        "OXINEQexqKQIm/iwwYOxtuvnPVjX9Yt3De/LNgPxBe+R2DA/0q7Jh4UN2SjkGF4LkmWcvPDHfhugnpZxkbH5MKYGR8"
        "7Oxb7ri9VADlpv3/Q/aEBJ8nZg0MMlQA/b19LI7jGbLwlEvo7O9wgcP7Wcu1YWVsXvYX5eaH5Ur4jVX3rLuLAGgEwH"
        "1vji/tCU8qaElHikDzCakaEBvgnxbE3+fi64csfAa6J/75fHQQVgbZvwMiESz/aKoAxkbPhkjAp8tU4HJjjFhMLSQo"
        "/BVUABoyG0ua4/uT4zBq8PiEiJwL7PAGUKrn8g50t+PT6zwFSvSFwn4+GlDvLbXE8BgKTqSjAfh3WtiiVCGgIGt0IO"
        "G7qwioAoBtCI9rtZpxGSLPb4/kcWSENuIuKojoOU/YtVLRrx85zxsZpZb+TrG+/j2HveCgr99+z91rSgVQbkr4IwKX"
        "I7TAm2HpGTnnRw7scSTvWLKuIwjHPV8/iowSchOYQrA/G/+nLoC0wlEKsaUAcYTckWXSUREkyl9HBSE8RUAYd+sKMO"
        "dYKgZuLXXkWW4ptJES9sgSfb5A+8KOrx8F+AKhlQtrURS0D3AutRIBlJvcms3WS2vVmkICqYBoBZARfDcluPgcc9GA"
        "m1psYbsPm4uUgJORmPHlswiAe2iAkpuUCEwRQCrEBqprYaKKIMLHYssXyPvpuUQdO9CcKgAp/FweR+oxbdlj4r+7wi"
        "6UQhCEM4jy4/8KkUQBEjGKI8uPcF5WA5ab2d5mQmUaAcQVL/7Pg5Z8uvyAVgrKT5bCkV2U3DH/ji/vhPAK4H2A7Mvj"
        "CaQwRgROK2E1iiCynEAErgFFBKm1jsi1kSuYWgFYUKA/uRF2fE6JQLSgh9yEiLgCyk0RHFWCfT3fTYA3xyDakLp38J"
        "lwT4jiLRVA6QIYgdHHKQdAhDng3xsLG/Dv2ykBzZPjIpWKgBd7/JkYfoDk4wTq515HFYR5z8oiEjgtBVlbU60cRAr7"
        "pWsglBWOEscVwOfVVh0VRCRcRWAUAFEI0mOQSjCy1j+yZGTG7xcR4QAIQYivl0QOCaj/lhKkuMOjA6UCKDeXBNREIA"
        "oHwEVZEzBjUQCacacFX7SFolaYw1bd9/EjH/bnKIIsN5BKpWH6pQVPrEJAITKpwhGJDihF4PMFiVUEaKETZp8v5PKk"
        "GYaMSdHUikZZeRqWjEh4L1bXWWFnyiWxzyHU+0l/31j+plC8hYjgi/CybywVQLlZ4dBEIAgFLhRdExAFKgId94DkBY"
        "TQAVMuAxOWBGsXoXWtuxV8LeQ+IrDuASX7XBclKlAEXL3BDLEnhHPfcAIo+BENG0aWOFTnUqHMfz7qAtF0ZKY5Aocg"
        "jCwpGFmiL0qIsDvRBGGiGenfokKPDMKLeekClBuTSUBHwZI73hKAaoEYHmDzcgHSRS6sH8xT+ed5C5Aoljzm3rH2AW"
        "WQsfpKYWWTgtznl+4yCrTnU1vGP3FCb6m/bxGARQuJFExjnaPEQPNEP7+ISKUhjRgwkl3oRgqoMhAakSjOoDC0mCRG"
        "uZtoSckBlJuC/7NBEOZGNFc+0kRgJy4AJQVddGALbJSl59bfD8s+zdvnYesfYPLbpfrmRwYYcSWilK2nlp0IquUGSB"
        "hOcQURcRNSJWHJOpGQ55TnKNEXWXZfEwOcKAQSKRAiqwysa5I+ZygXQChy1f9tUcGD8mdL715WKoBdHf5HBBpSK4EK"
        "gApVp5afVtYxhQBShM0DUD8V/ZDg+758roB71j6KfNhvcxHyuAL9vo01Jf68DvOZXADnvpuIE1IEhi/IVRKRV2TEJT"
        "/CPLdAcye0yo/6/YnOBfBSg6ENgPzcMeF64Jo3wFOeBPtVpQLY5QlAJYARd8hAbDHlCJRTHeiXBTO1bN2UWBvJ41nD"
        "TzIJs5V7niJgOfA+LzrgkIR55J8bMWDal440bNYkn87OI4Lv3c9kBJL7hhNw0IKO+ZPXo6E7lg0ZWreAmfcjVLaidl"
        "8cAlCHFuGc7/9rFFC6ALv4BjniHzTxfwOVU4GIVVpwoRugBFsYJpu71l0wD/ILpQxCDH1e5l4IzoetP89LA85LC3Yq"
        "AnX6r1CcgFAxfxJ/54qhJ26CURKSINRWOHFCipGOLPgIwOQN8Ayxp7kAxi1LYDgDjQY4TRqyVYURyQLEz8CJ9afHpQ"
        "LYxTdY/IvcMGDk+IlIBEY5vQFU6NyQfNnKXMv+U62Ql49P/dQww5+f6hv26/OTgExnIJoHIF0irxkIT0i2nevbp3UC"
        "zA37aTgOfnmkKv6STGYhIhrls0ckXEhJx8RpR0Z4AZ8kZEZxMROidDMEI+gFGJPf1e5xqQBKFyAinXK0wKhQW5wTCm"
        "TaX7ZQNSPnzCb7WGY/EJLLhPBCQjsFOO9V+eWFD0M9A+T79ZN/tNWm1jpI8iWkYEjYRJ52fIEhFT3lErmViDpvQsgo"
        "CreoQCmASN03hUvqPSNB2IhcpR4rVw8qFL9UcgAlCegSgZGt4Iu8UKAm7JhZkArxCyvyCEk5gfycuenEHYXwMtaelv"
        "Iy4hJ0kONfmP/vEob4n02zVXUBpKkGXpsklGXnxlpHgqQEJzaRx7oNBBFwci5SaMFBGSTJyEEgCXMzioU5zgsdItqg"
        "/n9EvgP4PH0lAmC7dA4AyAAsiyhy6uUjsscyEsBtjFoIh8znctFZpp9afqdU2A/t5cD7IiH1M/cyrkTgOVkA6ke0Sp"
        "EoE2by8nUtgCb6EhNXd2oFBEn+oRmCnGbsqRCdaTBCy4vVPAKFFlDYzesEXBGaAswylYZEGZBuRZED/eFzxm5SUKkA"
        "du3t4yADz3HDf9xCRWU9TLMMJtq0XTF8v4SZnGWteqHgB0N4RdV/fj4A7QPo+fxOPYFPEjIjDBrGRwTG08SfKMPwWz"
        "fBqRrUQkuY+shRBAl5Xm7CeYl+HfOcPNOgVCsXrYzT1AGuFHNKxGp+ABOUaGg35QJi0xugVACl/+9kAFLrEFdMA4nC"
        "hkvcCfVxN8buh/B4AdkXrOrzqv9CITxaK1AYHQhDf/2cGl5Lfz7xYLtWBLTijtYIKEVgQoZGMdgeA9ptiGhfgdDrRU"
        "m2QalWwjqEGLmtwRj3XQGNDiLW09XNxqrjKq8jtnwL4/vBPIj3QoPQH5UKYBcvAopNJ6CK7AVQhR3vF/das+W62XBb"
        "KHPPS8PNFdIoEMJzk3lC2YB5qIL2IQxlA3JPAchSXycdmBOfWsfWScqtCvVxv6EHKRay/AFJDzZ1ApF3n7gJPPLQAn"
        "EF1HO6fQmFYWP1MYx7k23esC34BOy18apy7aIaZoKWCIDtkn0AwRvkr0KrgMJeqVTlbbVaMUogzg0TKUJQyT8N4XGH"
        "ZPKEtCDjL6+mn5MQYTCERxQJPsYcktBXJiwnCciSgCI3HVh4df8eQcgj12ILNz03xB9YN8EiAr8OgfYZyLoj7nPqmQ"
        "XCQwMI9LERaaPZkHsdlIBUBpOTclpQqQDYrjgymR8Nwn4yDgGpgvDXpPDDcayUAGYBhnzEdPyOhfshOD8tn7+4dp8X"
        "RgfCUD+jTHKfUykIJTSW6bcCJvzSW0cREL6A9AMQmdRgYSsKA/wBRQ+CPL+PAOjz6r4FoQEmBqHBMf7GOGWo0UgVAE"
        "4JQmUAocCzX3joYTcvufP2JTvrWo9LcWfeOOlDeyDN98s93T3Ph1kAMAcg3Xvlbbfae6TPmK3Us6O1FIxMOYM4ttwB"
        "Hptzaf157F0X6/p01XeA/q19zvQcdVEi52/JOX2dYbntffoc9DnN9Tx9X05hkVEizMmTcCIOzO0ubNyfyH+ObBMSk5"
        "FHlaUT0fAUpZMV6YdO3UKfvFoN2eYNXqPeaMpBoa2khZmgtUarNQRjyH7z+MqnmiUC2DV8/+eBcL8ZxkrLbrV4q62+"
        "3qX/b1P9nFqA6ZF5pANv6JwP5xVzH84N8EN4Pt8QaFcWhUeb+UJCK++YqmSU1lSy7HibqDRc6qd7bkISyCOIAnyCaS"
        "ZKCULmuglRYtOTBQ0zWjfB3s+SlbrASIdmB/sHJPxPUQDeNoAXmHwLPHYOnL69RABsp58CfCAI+K9hEvDsvp5e1osI"
        "oCe1/r09yvoDa9wNxJFO6NHC51hxvaM1pVY2VlY9di2wscwUHSDpqK1/rO8TJOBYfPvatmORV8GoOYDgTEPe0c68qo"
        "VguFOQqgbuVTYGGqSynApKmp/gKlHuJDtFzvkowLcEzkVZRMBVWBfdPuwRCM1gpfJBJAAK4aQ9Fiz8LaCAtSUC2Ik3"
        "EKzTYAHs3yUtf1Va/65qigSwM7BGAKZBRiBzLxtqyx+2kWXs3c5CwSIjbf2Z7StQ1EdgR5lOI7yBJlqJINOSqKiMbg"
        "0m25NJvkWH+piDUHgIgURZBJBpbwZ7Nyj4OUOzJQ+AKAAQAJtsNJ4F594Fr/y5UgGwnWrsdx+QewMgeEPNRvNssKCv"
        "7VKwv2ZcAFAEYBVqapf5/ySLz7cifpw+bwaAhvxZ2dXivQMJ79YlaNM2YeqeBvDcS7aSqctMNwZlkjTkmgRkym0Rym"
        "3hkRO1GOjrA+EfUtGA1BVoNhp/c+Kxx3/16ptu2FQqgB2e6Fv0IRDmfcDiHw3+/sldMPEXNT1CvlT4uxg+lgq+RQB6"
        "RxTg9uG3pb96WhBn5ba9KiBO5qohP5BorMHTqAVGfIZgFFyj2WSTEA5UIcJZMD34H+DCT5cKYMfx6cFAR29LibzqEA"
        "j42ei/gxAPwmMVPO7qqknrfO9DD8iEEBT8boUC5N5lj/F6PBfJjsAagtuGH4wzRxkwp1GIzQY01oqXEtrJn3b2FJxU"
        "XxKUwLlzPs1IgK7BXDgugy4U0jsqfUkKzplkdVQA0iVonHnS8S9ZfNUNf7i0VADbZwhvXxD0WfBbHgkw/M9BaKG+Iz"
        "5OCroSYGnZlSDr+3966EGI9VfTcxr+o/XXll8qglRZVOWUoJCQuwLuKwSmHstTBpyc18TYzqAgZtJFoM9FIX/EDDUA"
        "cN6NVljBZqZSkz6WvU6lC4Nk4BroB3dgLnIC4AaAS9ADIcIzX/mSl113xR9+P1IqgG24HX3oIg5QHOv1YoBn30QBBZ"
        "/75JTEQ6a+llpzT/j1/fSxbpwGy9Zt3MCo74/QXxOA+m+kwqh1yUXBHcHmlpALCrkl6ULHNJrgKAZGWXNP0RA3Y2dR"
        "FNSDzzRK0kLO0zAhMwLrNgXV3ZWdUCXLE3T3MeY9VoHXx+xP/L1xJPycoSHgAyZQCZzA2MSx8DJXlgpg65fo7g0++x"
        "tRKMF/Pxyk/31WQImgGyG3wtvlowD12NU33iDh3QCM/kYLr69F5ZAm/ajngGP8u6pWAIx7Qh+y6lQ5hBWFwyXkCXo7"
        "hUD4h/xjzbHzrW75NUNvOH5O49AKrnMrmNyzyHY6UFjQhWq+klEIzFr+hLQRa4cQEkUSykzQaooGMSls7uw5kg9Yu6"
        "H1Lbj6wFIBbGkrf8iil4IwViAu+07QxseD0PaC1d+7W1ty38rXujxB14/VlNB3GWSA55bcsVTuGOfXCkMLv1UkXY7S"
        "0H0AcyE/hfFFlp0IPgsde0KexzfkcRAsB2Fk3RHvPO8sDsGZH+/n1mHnBo8rhl734c9aYtqog3b2tclGLAPRTXFPoU"
        "JgtpOw9PPDaIAF0ABXxzoNPFUEVbl2Zg3MwmzB/V5/0ilfgFqBz1x6ze9EqQA2n6wDLB/NR4sLRB1q1jPSZJvoNSB0"
        "NRTgHuO/K6E3xymUl3CdCLdFAMSnr1rfHpNsrl58o0zplX9HeAF/p89jsvB8ITcWmsB83wJT4cxDB20F2ioG+ljWzW"
        "D5LgpRQiyglOgsQn3fn0zkBPCFFnIeFixP8FiOwBsrXKgQssIuiBKh8wJ4DhrwH8tzDyqVNCJQraiaEKkEujBMWJus"
        "T35qclKcC8+4tlQAbNpx+BPhC34ZWPcFcPfDrg8O/naX9sP143hLBFlp5uz9qiT1qjJuX5FCTnPqMT5/y513sJXPPA"
        "NMb7/8UXsU5NfW39kVCsDnjYJW2w0BshyYnhXiHKFnIdci59Y8NRFc0n2ICr6LLjxUwli+oHuPCTXKW7bnT/9RA06y"
        "8fm0QEofq3Omrb9wsEaIMNQZ16rrXzpARc0HEJwKM3eVBCEDi9yDIjcCKgTsmqpZdwDXI5KDQAhiivBf7sgKYFu3Pb"
        "kJft8Xwjf94VoaqlPlt5U0TZbbhpTad5O53zJzK5EpmwnZ6f2WSNSc+gSLOsh5wSCeyy6/7hoV7rPwvlZNE39q1eyO"
        "FqDiperScVo2ISgqzuTj7hyBgNxth6SeCE0scRSJPeSOsvA7IbsMPnfKpp2Oyc6sBHuOs2wIlfvsBiVJvS/U+f7pWH"
        "VnpoNK3orTvo/VirsTA/O+t7zqNS8oFcA0t9vuvmscfoXTQLAvS5KWI8woqK6ApxVa5rpWwTmqCOh1Ir32mTWr2T0P"
        "3q/y9kk+fUwr6WxrKJ1TnpdUsjUFUYjtibH3qEXOw98LQSv+98U9Aae6wpmhEhB+SsQyloNoiLJyEA1BYa6ColwIN7"
        "UbcURqPGKDKrtgjX6yVACbsS1eettq+KLfAwL/+yTdpOC3iDC3VK52QhBAyz+XBM61EtWySu1EGdDSWaeMNtD+Cy0B"
        "pvcKxmZQAMVUh5TIjjWYsSiE2M5Cdy5qoTF6Fsjxd5WBa921+4OfEZtyYDquUB1/XcQQQkrZ3ow8F5kUoRN7Pyv8rh"
        "KA9fHsUgFs5nb9H5esu27J4pfD4ctBeNdbIbaWHWu0E12nnbHyLXNtFjVk3YAf/uJCVaEXm1p6zRHEpkovcurprfUQ"
        "Xvvp/A3nUTThPUxCSul4Y5KNTEywjeNjbMPYGBueGGejIMx1+b7aqAoQACxOWbdxI1uzfoNUAq12f7TVtUCeUHPmIn"
        "6edR24iwTwtxqH72rNhvVsw6ZN2JjD9PbjORCjBRzEOFy3aTL9jtePjbPh8XE2AvcnsMEHrhEhctwt7rkLnLSGt1Wa"
        "SBxXYrVDTUicdoba43WvOPmAUgHMwAYpln+Ar/6dIKirUmF1LTsVbN/nD54TInPdhuGN0rLo0lxTOhuHpsNEplEklX"
        "rRgQVHS4TCj4tyFKrKNoElG25MsE2wGMcSyDEHoQZbzibhPU1A66kGKqtCBNBi69evZ489sYI9CvsoKJGtW4bTuSLw"
        "B6Bk7hdYXNxGxkfZI/AZVzz5BNsISk8PUvUFFB9twrlJ+P7kd4jfOTb1gFU9AQThGHynY/D4GMTuJ5r4HSdSKQtnNm"
        "MOCardAGwWooQeG8FWCApI3YDoWbBOjiijADO0XX7dtVecesIr3g3C+kMQ5t2gDXXUSmIjyHFIIcAiaMEePEf8fyQG"
        "73ngAbZy1SqZ2JFafa8DjmP5yZw4S107x3rEtCP4YMEauCCxwgxJzW5Zf8Bi3IE8khAXzrew4cT4BKziJqtB37vuKm"
        "dVHDgSYOBRCeHnHAPLNgloore7VxKTvRC52N4SfzXkNq6KmtgjdCRA2FkJwoxHSiVzHJTzug0b2NPA0+Df0LHq9GWw"
        "pDcV/hYINxTsYINP+C56uwdYBA1cGDYMhXNN+K6aUNHXwB5/mM/fFGlrN0XWGpdBvRlOwps6x0F3UapERPDJLWwfgv"
        "2CUgHM0HbJNb/DkUx7AsP6QxD698USysOXbWB9rJSB5QviViRru7Pn7HEsYbMgDTgsxKccgKMUIjUdl2a2sYweMPFn"
        "VETjINx1sPIMcwx6IazY18tqkGxUhWgDRjgkHwFC3wRUUIHzDYC7jXGErBOsG873SpY5Jj5rJMOgu81fCIolYU8+/Q"
        "RbtXaNjF5gpiLf3sIGJJ7HjTDlCz9Xwo/fHUZoVq1dy+ogtHvtthdbMG+B7MiUhh+ZvBZ/RnSdRsAVakLeXrUHwrSQ"
        "rlvt6pINXCPVsxEVPwp9oz7BxkfH2OTImKzuQzSFrXAqqtchFX7hjnSSp1IiMHI4gArZYc0sKhHAlllJH8Y1AVb99M"
        "QRaPTnrKBLci8i5xRiyOxw3S+v/K0hdSJC8lElEEW2D552AUzEWkm9sFnret6EhPGjzTprwvmewVmsb9Ygq/XUJGGU"
        "EolpV54Y/6vGcA4EGJ5hcnSUDa/n4CKMwbz6pmGsK/i+DBkVyZyF+XPmQP3CCBsZGWXrAR4vmDcfLNPmRCPEFos7cp"
        "IfoKWLOw6UrttLcUMTBHvjpvSzzZ41m82bMxsqNHtUM5BU+NEtrIMAj4LyHMemLKAABwb7WR809YxBcdJMQIkgYvge"
        "axC6A8TXgBLfcVAwm9ath++5znqiCuvCXoC6i1FA+PH9h0lAZ6+99sSTDvnN1VfdVXIAM7j9/PJL6iB8ZwEJ9h2wmk"
        "/6whzOAcj6/S11/YZNwzLvP46tpY9Jw87I4wLyRkQJjwXEJYzCL/1QWDVd0Ga6d9YA6+5PrVKMFowM2TQJMVKRwCIF"
        "dMBhwddh3wgiv36iLn3WdACGZa5r8DxDAwNs4dx58lVHgAcYAZdguyIEC4KFPEC86X/wdxoD8m4UdvyaFsydy2aBwp"
        "PWn4xZb+J1SIhONthwtZs1B+cwkH7WiqtqDKPbvozrQa6YwINt3eD76x2axRJAChPY7guUiQgQmU6DkYgHrX8cmx6R"
        "fbBO3srKnoAzv939wH2NZfffd9mi57/gSvh53gBf9ACd486p766ba9JzRLivvfkm9hgQSzq5p7u7O5j6212zxUW4V1"
        "QT0HBhT+rrSqIJeQjoKTB7wVwJ+6XV9zIHGcn+mwC5XTGasLs3JuzmdQlbsj5hD27CqEGLzY+aMg89NglFzHSvRaEY"
        "Htkk69QxUQWr1TBBZXqZgJScC6QFe883XSTAcoU/3bAHP0L/9cMbwN2psP333Bs+V4/pZSiJUGT66022cmyS3TBaZY"
        "vHu9mf6lX2VJ0D2QeKF6x9T5R2Kw5mMyL6AtcKM0wb0P13EjiYBFy1qory8EBcU49wRwWlWoXLRiFoSBrYONQcNwae"
        "ve++P33wsUcnSxdgC2w//PmFd3/w7e/CMOFlsD87hfqR3FsttOJg6R03QJ1T3AE+ns7li2RzzZi04KbtuR3rr6IEEi"
        "RT6E+OsZ9cHQS2jr5oXw+bNX8OLLCuwtlyTSS7AO8+MSbYH1Y32Y2rJ9md6+psY52xuXGNHdvdYvOicXZgpZW+VzKE"
        "BN0CJDDnz50vybJ1G9cBIpiDI27YjlDvyxXEdiYn8xS1bRodlgptHlTdoXLGz22n+XCpJFbXW+zeCc7+MN7Flk3GbG"
        "Jdg83varLD5yTsxIVVtmh2zOZ1gTKISNqyl8qM4bvBOUPydccgrIq/X002VPWLklPXJOUBdJNWHQasmFwA1SfyMLim"
        "F/5kY+kCbKHtP392/gPwA54KbPhVAI8brVzWXzD/3Cbw/W6583YV+gvBftKrH9FDbLvGhlJ3dFJQM0lJPw5WuWegj/"
        "WCNS6aGdiCh5+eaLGrn5lk37pvhP1i+Ri7AxbxBhB+bDy/HhTWnxpd7MaJGntqoiFzCPzkFlx4c4fmQKfiXlmj3sT8"
        "CCZ2kHp/1yngqmqvqSwsFl2hAkBFQK0xXoNu0fLJhC2e6GKPNWpsDHigBgwPXT0h2M1r6ux/Hx6T+10bG2y0lRV8is"
        "C6gDvo7e8DbqAbkFgaIswkDpPfPvLcgDiirkDqDsBv/tySA9jC27+ff9593z3vhycDL3A2RATqMu6fqQtokT09h40/"
        "MKssJkw/5QAs+28nxcoEIDMTJ6sFUMFgGGpStFgv+P39ff0mi81N5Env12GNPTWesFvXNtgVT02yq1ZOsns2gFUDXw"
        "BzAHoQwoI12chqbOkEwFuwdE/XUz81EW5IsBcXMCxeVGZ4HpUA20qlADOCBMhxosJ5qIQxqtGHn0shKE0T4vmn4Au8"
        "dyIC2N8NPj8U5ACR2gXgCHQCe2a8xe6E7/KaZ+rs6qfr7F5wqzY0hLLgPFjU1A1IamDWLMgfSOR32BI0I9hNa45oCD"
        "BKcwJ8TgCe8/SSA9hK25I7br/u2MOPrMO3fhKd886j8PHlv78GIOaIKvZJqwqx+q/LL/31egzIiTFOqa9dHE1QPBjr"
        "j4HNR8a/CxYUC/TS18drJgW79pkmu2jFJFgssFLNdLV1g+Av6InYvn0R26evygbAB27CZxqIWmwI9vlQllrDSALhAi"
        "IZ8kzRjvxMqlx1i3AAOZWBM5U4hL40kn/oFwwAh4LRDloViUp8GMKCD0LKxP2tbjZc6Wd79tfYHj0clEDKpzQwLwAU"
        "wQh8p4+NQPgPnmt2LWILurns7hP6HLr4BzpCQ15GS7p2Fal4ssVOXCVj1RUHgH8j+wTKhqHNtHFooxntv/c+lz+0/N"
        "H1JQewNSAl518FFb8JLOwHYJEcYcKCygWIlQuAsWVEALrYJzNWy6QEk3CgcgF06SsZL69GymE4Cph6EN6BwQFWBWUi"
        "eJgqQ8vyBEj79aua7MqVDWn1N9bTuHM/5AW9cF4XO2nPbvbsAXguiOkh2bUOEMADq8AlmNwIacMQsiK9CPXi7e/pY2"
        "I2+MaQCNOCBbijdggUKi9iFoTpcCALTRzSbtbwZJMNs26237xB9toF/Wywlvr36wAV3LchYRctH2X3gh+FimAtuAQ3"
        "rarLfr/1VpUdMQeIUqUFhFdhhMlZffD7jch8gQYgitidVUDCgm4EIJsPAOvlQFhD+8GlD5cKYCtsX/mP7yPu/d6nPv"
        "bxX4Eb8AsQ9hdZFyBSewzs8mqZOIMz/Qz09+bmObtyCzilk1WNuRb+llyYcIzxfGD840ocWNip8hhpJOyO9Q12OcD+"
        "29e1wEoJY/kPGKiwlyyssZN272K7AYCoRlw+9wYguLqjfjYMvu0KUB498BxDmBBUsey0bFoJTPmmMXgjPN4hW3+mBj"
        "aSGZJ9GJWpVW12AFfCD5/9qVYFFEQP+7MFfezAWZABWUmJunH4shZ2JWwVjPUebrTY8tGWVP6Pw3d246pEdv/dHdDV"
        "fn1xEAkg19MF3+HoJogMTDTldx9z5iYt6QhCbOcw2sSgihkdj7dJXXwCrr665AC24nb2d76xEn7Qt4ISuDVbKZgeO1"
        "Y+Dsf7jStBRmYFCUCRxv2RNq51d8kEFD8TR1uacRD2u9e32I0A/e9eD3UBzUT584LNAit24u41dtyCClvYzcwCxQU4"
        "uztihy2AKTWz+tgzwAlshMVd9+L9+DnQTcGWZthLYVu59JtthUB4kNBMQ66Rw79h5iMK9vqoi82d1csOArTUV0tDfZ"
        "LMg4O9+jh7BSjQw+eAG6SUNgB6ybf8cU2TLV7dkjyL8MhAExUAAhfTiDE5C39XXXtAR5rhfVsYFDmW36QGV9LagJIE"
        "3Abb57/xtSfhBzoRCKWvwz5J+wFct+RmUvUXZVCAM7evIAFII4GUtAKI2QXMPzDJFCnQTDRECMhQX7+qIYm/tZMJay"
        "nhB/dU+qeHzK6A7x+D5ffIGZ6Sgn193aw60CvzDNDl8IML+F4HwIKh5dxRN8xhGIToSU0OXHEbgaBAjsBn7+qHPH9M"
        "q0aSllhw/OoRSf3ZYAWQAaCEGn536bnJVppncTWQrfcPQ4VhiweVH3JF3fDcVSAf8XdNlNX3m4noSEBq7SvEDaiklY"
        "LpupoNbcMXlQpgG2yf+dq/DX/qK1/8W5CS94Hwb0j9/+G0/l+H/mgKsOID0nRfrwJQTfL1/UYhZ9Wl6agcyTcQPh7W"
        "E2DtBXt4uAUWaJI9OtJ0YG8frPU9eznsMeuvhAk2XMgD3VXJ9q9qcmC1ExWuEl5fC7791QNsXiFhGvcH4d8ITP4zUO"
        "fRA9/BABC0PMDq470hQAV7gyLdDeB+NbYn8De4BcKsy2S0RbCWYNmpTrCj8Fd6uyTKskVMtP26QgveSPaKNhy6PDiO"
        "FsD5l5QKYBtuf//FL/wMfsKPguCPPrJihawtd+r7Y3sb6SQgQgymSoGbNF/fuqNrIdASAVsfVytOZSBVFCshNHUT+P"
        "B429DnVE36bMhUec5gSk7xQOhQL2yMCPTAwn+8WYUkGBZEATvjJtOrAb2tBQWwopH2hOyvxV7jEVeI54Hw7w/faXds"
        "pwEJGX4V7K4NQL5ubMpQbCiiIYUXXgMkWhYliaB24gb+x7rXZCY9WGqfD8IEoahUANtw+8TZn78AfsS3QsHMpRGt5i"
        "Lxf13tZy0/Nx2BsALPZqHZ3H8sKUYrUQGhrBC/2xF+OJwAU/PoSEsmqGxsJLqAwKynWRC+2qs3jWPnJQ1xBW85vNcH"
        "610MkCyUAu8IKT8zoADgQ9bBhwLwxB6ExKgESE75XRSEJQfBj9q9B7/TbHXU/cNNdicQsZAj5ORU0OdCHx4ThJosTU"
        "wKNS7Ra0dnaDpRgSjtIQi3B8N9XiqAbbz9+KKfX/XQ8sdOsD5/nCH/XC7AwjvuEdv6sKUalcjy3ko1IPxpnfoqgJsP"
        "gN/5yKamZKr9rRteY1YVmekweag3TGkVcO3jEM56uoFxbmS52U6NAoRIQ6f4WZ8B5YmfHfMiuqJssY+T2APf0xAgsl"
        "rEM9YbSUCss1g+ImTikJ+rkaIALBjqZYkqTso0PPUKgyoVtz2YKgySt5AzcFSpALb9QtobhLnHpP/Gft5/nNMFKMrA"
        "UeP/J6l1wNp+XX7qbxi6wrj/YyPQ/cew/kSLCM0lZKML9JirTC1gMNhqCGdCIEHxAIIlOzX8Z/IzDoOmg1IJtgY+e5"
        "NFkhPhAcGnRUtJuCOgbBiyCpXAMP4mYe2JwluDtvD4e+naEe4lBEWclAebMuHIVQqpUXl/qQC2PbP0j26tPxH8OPbC"
        "gLQ+wM6PFo7gqpx1VADVmvb3MgKM7P9yEP4VIw1SOuxWEiBKwIKgViKCll+/LJQNyOy2CYhJrwIybCUw2XUTqtre8/"
        "2nrwKQ/V8NxOdT8JknId9/E6Cf8VaO4JMiK3S9BAtNX+aQfJWAK1BXeRjZ58K1goVcLaXE3XJGbpqWOgIfeU1DlVsA"
        "kYWXnHjci/cqFQDbZtOG5ktfLJP7HwWaf/oKIsrU/QvV5FOWjEC2nty98J/e0Ho9NpImpWTlNF2gY2DJ14w35bV5tQ"
        "P4euth0T41lkhF8AxUPT7V4IoITHZi5JZmWaL1f7pZkZAdY/oYRhUFA0smm5gF2JLfaUgrYUThPuAChhvCSdl2egfA"
        "7xqBa4YkbyICMxBUGrYR+oqC/rRKMM0HeB7wBHNKBbCtLFHE9wAi70WS7DPDPLSwE78/jjNNQJnXt0Zbf8kOYzII5t"
        "znCH/quwogrxK54IRfQ5gOr4GFinC0KROF8jgAfL0nxlpy0cL6Z+tAAaxuRLJCMEnETu0CIAG4DpTdGvjM+NkfQv99"
        "NAlMDuKqt18q4PidyhoL7rkBHIuGhKzHWF9HBRNMLZc5AdhBiGGthWAsNAAlJfssqay7BRsiUCkH4BE+WyqAbbRBNd"
        "9QHLnWPnLy/ElbcM/602lEjMyel+E/ZIIhXMQDoT9t/bG0F1zN4CLTz4eRAYwSPD6WpBYpL5IAKOJuaBSAi3qNJAKh"
        "k00jbXG9MyOACSAA1zYjQD1dEvrftwmKgcClwoBKIlz2Hu+uA6FGBfEEaIuJRDiCbxUqpGXDc62F3wf0qtNtiRZuYX"
        "0A9nPEPIRQ63CuMgIrXqswowQUGQjGZUGpALZdHPnsiIzx8nkAv+svDQWGqv9Tdh8ED07L8F/Eg9B9soXWP035DYUR"
        "9fPJElaIFPxxXZM9DKtyUvmuuHZRiWyCv38cVuk9oE0ehMU/jooF8uFXgUUcxgYkidgpIwEpAQgoCnMAQAGsT1IX4N"
        "ERTOZpsMdAIW6SRKhyyVTC1Z82ttgdG1oyzNcS+ewE8jOrIEVwuBl2JyTLjwgvxpqMlvrd3HZm3BCBkZMLQGsCVLPQ"
        "fU940XGHsLIYaKv7//vhtOEUqln4T4maKK8FuB4BZvp9CtXFhsnuwwJ8xIrqUusLPz6GVvtpsEJjLZHTeFOYAZlotX"
        "6PwX01/PLAoVgy3RsnExm3/h00DblhFQ4VSbkHtEejuIBh3wOev0+9Jt/JQoAo8Gvhw24S6WcWsqYCSsBXYyNPwU7a"
        "rcaeCwVBcyAuiIoTC6yueqrOlkDOxXhLl+8IW6NkWxBL5YAh2g3w3e/ZHTHTEZQgAfx963Ekcz6EspLCLREkhUCRVx"
        "MQmX6BsJ72huueD39wV6kAtiasifiL4Ms/wFr82BsB5pYDU0XATQIA98RWpPF3lsaBqdjR2QBI1q2GuvXxRkD4BSmc"
        "42lbsPvAZFXU2LHHxyry+ZHsQl92CdQPoIuQmDZa0PsOOwo1Y2n1sM6hEsU71W+HxVsI/1cD+z8sOMm/gMxK+C6uh4"
        "YfSPbdBynW87ojGUXBIitMuFoO4ZJWEopJ2NRe5FXWgALA9muJCrNSd46r39dwAN4odP2OIlo+TvkAigDAFRCTk1gd"
        "+NNSAWxVBRBXbIFP7EH+2M4F8OG/rgA0df+2AUA6Nlr1Fay4KalU1NEirZ3A5J8kAAA8lSJSxHAvQFuMGGBTSzlOTF"
        "lB9FP9kPUYlDivkgognYeQ2qdtjwH4DFUZ4sCPSeX/j7TiTEj0MYBAz4zXIdmnLguoOEu5EoyqOKBLW33umG8p9Osn"
        "E1linLA40zdQN15FYW4IlamB60KQjBCFFPLahOvRYQp9Pqt0AbY+kPxGhbb7UhpaJwNF/gwA0gTUsf9a+DU2hQURcW"
        "EQgOk/TyYGTYLgr4MFhoogv+W+cMZboTCjRbftfGyHHjM1R7fGgve0HplxOScRhb/qKqwd3CGQCACLgCD5Z0xEQX6g"
        "0RI2m4rR48JupMbVQuEfaWQ5FKkM1O+b5oKkKdy6JTkdW8x5eF5Ahc4RTKMD3S875kXH/v7mxTeVJODW8P8POvg5IN"
        "hVOtgjzsB/OxMwJogg4lFmHbnTAJWQRmHmmqkFisLcTEJtRN1sQBMT7LSAH5EBCMX6Zix93ZYiAoUbZWQ7cjoQfm11"
        "EPBh/IxJPOPvBb8vRFa5UQD8L0rJQF4wRNR0CnaF3YH/KlW4F9bWq8oowNZrE/Z+EOx+J/wXZ5n/UCcgtwNQQLCUGY"
        "i8r41CSMzwQ4veFF4qoWjXjiNPWbjX1yEMsUEKR+rPBv9e7FBpf26nZdU8dRg4APyMMz2qSBKKLSRpc5KKeBrmi0hv"
        "wMyIc257MeRODSLlwvCXb3vJ0cfMLhXAFmf/DxqAXO2XW3ImVAQUB31/twU4Sd8RbiK/zAXP6aVqJtdgl16TqZcjpL"
        "k6IE9ZpO9pEt4PzA+BsVjYCjwJQGCxo3UB8BAAVFvCJxsGdDMmtsxrYZ7ABE6WChsQiMRgNKZSONVIGoKI57sAJCQI"
        "aPQAuO0qFcAWJ//k1KBjoyjb3YcWbkSUG6CzADQDIAIOgEiZ6ETY5BLa/UdfiO4p+qjBRD2RI+hCtEcE6m4DXn+TiG"
        "RWW+L1HxAOeNgGiGCGkoCwd8IYTk4S0RbROfg71hMd0mPBLs4yYsB4pi8AzyQERUHhN70CVd8AqA78aqkAtrxF2Yum"
        "/JoOwF4kIIMAYg35XI/flyE7SpplhnXoq/TiSkQRlO/gOEdooXs+oIBYugJNzQGEFBYLKIJtPA6gMwWAE4CY/IzNLb"
        "A88btqqChLUV0B59z9AvzxaE5CUOymmUslEDnFQXDcXSqALb/9o1P0Q7v8mFyAOJsHoJqAhoyxHRCV9p+L1Gx6XzqE"
        "Hg8umXqVjTYVv1+I8KWCZcQ5UZN0MXDQzKEr0/+3G1awYwKwqar6EsZ1P94Z3/D56zlfjRZ8WYod2TkMrvBzwwlQMt"
        "kkAkW2R4BGB7DGDj/+yKOfVyqALZf9tw8I9HNcWB9n24B5UQCtHPT8eSqPGWFSkeREJJlWYTaMpe93QvblXVaMClKY"
        "bJGG8DmEnBZb27M/oNOgmwpBbck0Z/1aItBaTPMQGA7MgAPu9glkqkOQmwVYcTmBikEA+8G+R6kAtlz13wFAyhzsQr"
        "LIHfoZkw7AmQ5AvC345WqMVaPVMELvcwDMT83JiwaIKbgEnmDLUBlLlQAjPEQ4auEige26fkAhp/pmui5tFz0vVoSY"
        "YIW7tv6FI84zCUGR2yMwsnwAJJJ9rlQAW2gDIZ4d+40+YpsG7LcBT+f/cVsAxGnhjytJusEEXpuAkz85MSndgEwxkG"
        "IKomiaEbKOQocq30DCZftehfDfr8gIP9veiUHFZzS25NtTblzRpDOcEISjv+LYjg33x4ybnADNAzj+P0UAFaoM5pcK"
        "YMutnS/48N+4ADFtA058f6IsWMYFF44M4o9djSow+QUq/TYMs3EYN0bHcVFlEAua59eBZRd5lgqy0rDwBCsQ4bYK97"
        "th7+WJvJ/vPIgwnSAC1KDYzqKCSkB78HPCuPca3OJnxc7p+F1EkhkQm5WYgEHcSIQjEJNjY2xseJg1xibg967KrA/m"
        "CT9FAnJwaBxlBD+m5LN9fN5xRxx1LCtTgWc8+++58EUPOj3aSO/2TCcgD/4bAlBX/nFX8HU+KC6IyclJNlHfBH+XIo"
        "CunlZqKWKFNAQ28hRyJFVDcOaVFqqUVB6sDaDH+MP0cS0AKRmFTTEH4QX2jRtsNxCOLnzfEQv8Pcu8lpqTaxQB5+YT"
        "b4mcnunm6cjRaHPhfb+gOinf+1pId4beKdI1QPerjjX98KHtdzt1HYPzRCsq4ouIroUzHjF3A+YDovBPbNzEBBARNZ"
        "wWRKJDXBUECVJchId+gxC/UajOCYD1NhfW4RHwlzeVCmBGfbroZNh3i6hv73X6iXOaf0rrz3m2aIcKqeCqJTRjvV1V"
        "VoH4dGt8Aub3QUEKjuaCqTYVWCzVWrccTjoLhLRPkUic6eGiqSWP1eJLj7m8TZOLmDpOb7vg72fHMHY8EmrBprMEZ+"
        "FAkUqL7dcdQxvsqgPhUsGm750VFyQFi5S2rQLohi95j54aOxKU3/z6hOwINKYyK5G9H9O1EElarZeoEl+9y4aeLL0W"
        "CcUWs49rQR6Mmfx9EoD5EwD3GxPjYPnH2fj4OIvA96/Bmqj2VEEZud2hBS15wt9U2MrASNWaVEzoz1cIqTIQE+xMmG"
        "r9nZuW3pqUCmAGtsNecBDKwDtDsX76WORlBtLruGchw3X8qbGt4g8t0r58uMKSBEd2wQKCCjUej7LquGBHVpogoFgX"
        "wI1A416TsLbFBmImZ9ppRVBhrmLAWxwd1ltJR4jFOusMXJAasMo4TGSoCjPyQAHoBmZCcOY1MtI1RIXW3+tSsM0Uge"
        "6A3Aufb6/+HhiIMsmeB63PJpr11EKLtLtyHZOEmlxGCnAEeFNVT7bUrT6GnwHSiblUFIgWjIJQU5n2a46z0dWj0G4c"
        "Ao6QeJCAO8eh01IVvhwcUSZDeWQoLPWhuKo0FMQlSFuD0fkTFadUuGKb0uwnhOAlApg58g+3Y2iPPycKYMaBe5GAnB"
        "bgzBcmoX9koeoAJOKAmQA16A7EZZuwxiQoAZg+1ISF1Acr7DjoKVevcPU8aStpvK2BNe+JE9Yfc9m73p5Ls8q4QgNc"
        "5SUg4tD3OUlZxoVWlQMoeFZoPasuOlAEdua5rpoVxSzZFm3lxqUSqEY1NpSkk34ZdAVKVLRDdmZSCVD0MaFmNup8jE"
        "nZVQmnB8dSKdjzsOjxd4BU6jo0EhE4YDWuyrHgvV09udyKHVhKyoe5zSa0PQErTmOQSmxJwIoaHzZZr58Af3JVqQDY"
        "TJSPiudX/W4/mSpAkg/A3enAnHQAEpy2f3IVAS255apkN1bwrwJmuhu/yq6071xDqKs4EXJVRwANhVgt5irJBBWKvs"
        "6moHLl85tb53GanMJyrHr6ZjMlwjluAL1ue3AG5LQmyMWvydCZssIm4qEF3kY49DmjDFiqJGa3LHeQKgCbo4EcDZKq"
        "urJP/g74mwhb/i3adD3g5L7JOFUJaC4hmHYK1ooA1sybSwUwc/7/x2Kvrt9p+01mulMEkFrYNAswxMW5ghByENJHon"
        "T1SGygu9N2CyWwRohdgY4i9Xc0CcUMo+RmJLU5NiEnJ1rpvU9PYbnS7Vp/+jf6UY86SJHDtkMCzB8YKmxfBF8UBen5"
        "IVT3pEi6Uiowq4WZKBKuoix+PofovOrUQQLpeoqzfr9KC66QECEomlNeuOiw/ZbccftjZRhw87L/docf4mja+DOiwu"
        "5MACYRAG5DgNQ4hgvrs8eiIHEvTSFl0sLE3D3WqcQ88PeiMPlH5NT757wZURSAFMGkIEGYxKmJAttOy8L1d5/eVsz9"
        "FIVFfLNKzjNaShK5cZTTJajiNAyFdbov3A6UeQCbX/03H/ZFFb/zj9cJOPY6ANlMwIiFZgAIVpQS7ApeXkowD/YBCV"
        "8rvCQEJ5YvAjH+QM5CWJhD773DIiGR6wRvg8YBM4dC+Aw+o64RcBOCIhIJ8CcHR4YTgPDjV0sFsPk/wD40n99n9x3I"
        "71QJWkLNFzmRI9yhhLrc1HvHfxTFmf4iXyxFYQnBTFposZUFk8/c8824h8KnDTm07x95Y8L8luFqolB3qQA2f/sHmn"
        "kV6e4/tBW4lwfgdApyg7y+Tc3JnBUdWPQ24iW2k9rbrSkivLP7vABs8E7eCd9aiiL79HTYTMXPCDRuQCTzAcAAHXDU"
        "IYuOLhXAZmT/gUDv6cb/XR6AxvxpVMB0AGZ8yk17duCOW5vdNJBvoc/FC67kgYt4IHuRs20PKjhBATQfQAo9mReglM"
        "NC2J9VKoBps//8MGDT9w81/oyDY795JlwumA0bCZED/TMinzOIg09hAfG2z7ZLbHzGtQgP+vjFvxcPQ5Di1qJORyj8"
        "L3E7s6QRoogzpz2d1zVoe6gOrOzABOBs4/NjO28l5DTkxqiQmx9ImFiwoLCftJHnmS73PE2xZWTSzDa15DumsIvNvj"
        "DvZGfPzkk0UeQ9hRCkvZoNI9IQIhV8bTjSPIOEnGPmWjN52J8sHMXzSgUw/e3IzBBPwWzcV5CEEX831yROthx3kmS4"
        "t65U+ic3Z7Ngle9Q/kDhvIKZEngylSssq3wL1/7mkbDCnfvoCrq7hliO4LtJSjYbMTHKIHEQQiIEI+ol2I6sVACdL9"
        "Wr4Ev+c0cTe1ligrlWXwRSR6OOrUmaE85FO/ERXuMI5a+qpJrtIcGGbT/1P1v049HwJ23g6lppERT8fIvPTBMWqggy"
        "6ysh6yxxHzeZiUlSKoDpbvDlrYMvcwQO+zNffkjgGdG+5MdOaMaZyBcSkcdCEzzJSe1AphCfkzRbahaVuyIYSUPejo"
        "Rzym+Fbz2WVHjTm0Opwlag3fuOxW+DAMKC7yoGWVrsuABhoyOo8HP+lZIEnOZ227K7rgBNegd+kdT6Mx/+exxAUFs7"
        "GjsJwDn1d1STU4hHr2MsF23Y10oy51nA0tDegkJs/7FCvsUtuf+9JixxvstEWlsNwek5fT/xfgPzu9H7ib5WXZ+k59"
        "P76jXUfWPV8e+Tgt89ce+35Gu0HisRwGZsLWzigCO7AwLPqMa2hj8L/TJmjps2Gdy3g06raHWd8HL0QzazjVUUmefI"
        "WmCeAR7cjioLZPlvNbs/bXaPh7IpHMVnf6+wFc+D83nnWAfQfyoWP6uwkyDUdxSNUjCwdp+A6tH7SgWwefnen4WUyq"
        "tbWrMzj5hhLh8QWjx0LQrZcoqHqoEy4hF1KDhhAfaYMd93oDW8hfKYI32ktJerQhqxBTnKTnSALcjxinMCiGdKgt/B"
        "uY4EP5fY60TwLd+U5KIAqxzQcMH+6G1333VHqQA2iwcQa9SX6ULBHBhOfyhnwehOsaphRJYTIBODuO7MKyzzL4pEId"
        "Shxy29zdS3OSHJrIKwf+eXBFpU4n+IjP1VWZBC6DDn1AEED+RQCcGyhBrLEaIpCn7nPj7LEr+FPr4f6st5LzmIwI8S"
        "SGufSzxD/whodAL7OlaWA2/2KOmnYV8CCOCFqd+WJV+YI/DMWTj4Q2khS4QViuwKLxBYwbI1uoU5BQGdYKICVMDDkD"
        "koowTBuIlF/vtuE4PjpK5WKR1NWgo1EtupUWwnXJ6wM0+oXAudb8lZjsCGznXuFoSEOCv4IeVSjAiSoM+v/w6NVQN6"
        "D0IewGdKBbCZ29K7l62CfOo74Ut9YRNRAOyGiCEWyYGewv/hfcidbawpSD0+E+09Z+5H+bLmd/Mb9Be9F1+u6csV6g"
        "BO2oRmP1eeoDOW/U7bWfyQ4G+Oj89yFUQ4lNexxQ+cZ8GcgADBnGhyMTGEJQp/HRFAo8FKBTAz4cAVLSX8yAW0Agy7"
        "cBIwPKvltHYSGSsdFcYHrbWPcmkA2pTDQvfMqCkhPITRhgMQrkYSOWgj7zmF9z50foJ1DXSjkrRTslBNMIss8EwJ/v"
        "ShPn3OzYT67TiBnPebiPyck2ZLQn9UChfBun24VAAzsAGU+hJMcflCK2VW5UQXlw8Q2cxA4haESDfLCQg5o45nBNFv"
        "DZXHCYSge07X3lDtvaCcgJdgFGzlmeUEMm6K3wJMdRLmqouRbo3O9Wvq1GqVBWl99iIry7KJNAFhD8XmWYfkHmOio4"
        "SesMVnAT4ooGhyEUCeIvCEnhDP0vqnvj8qglVL71k2ViqAGQoFyqm8SvhbCgkg9GLBlGDi/xsSULP/7qBKnusju3rD"
        "1h7k1Pl64cOslQ4Jdztc34k7YuccUIbAF36nbZg+Jj6/+Vuv/16WuAu4CFMV/GlD/XAoL+Tf56GG9v5+PgKggi5Ibo"
        "HOS2hK2J9Cfwj//Y6VXYHZTM2TRw3wL8AB/HMaEUjUbLdEVWiRyj/vhzWpwLDQKSFYnI1nxbU9YU6Frsh/DxGFlkjI"
        "eys+vNdCqucR6B6B3Fh1nc6cHqd97dxrBNfXeq4Ab59Sy4r85c0gAadm8f2Yf74i6BTmF/n8ofdFMwIlimxp6w/+Py"
        "iAarV6UakAZooIvGeZOOLgQ9Zq/z9JlBJQoUH8MVhBGDDJy80P5PVKX5+2CQ5ECtxcgYJIgS/A4WBB2H/XsF1JpVDH"
        "nJKWWuDJMVfuAecW5meuId2EjSugkQFj2VyLHDRQ7Ofn++qFPn4HUJ91CP07E/ysYsrkFuTmE9gioIby/dH6w+P/3k"
        "KNUCqAGUQBibhRJK3VIPTztfBrTkAnZtBSQN/StIPdNPEn8W26yKlNF/Ra1iac5/ICxvemx3pIpbqfCq2ws+u1IlCC"
        "zIx1d49TpaEsvf5PUGTgoQf9epx2Pspn/UNuwXT5AJFbnddhll/Hob2Assph+PPyC8z7oinliZBotKmsPyoBWJf33H"
        "rXnaJUADOLAm6DNsvrpQJIXC5AkoIGknkWRLRzoi2ET0JhwLwUYu1b0yYTIojujfCbMmMab3f8cFcxGKElf8PNe+DO"
        "exCBYzsgxKIHoxR8EpC2ThV5/flz+ICpRgBYB4qlYx+fFUP2KRN/7XkKP/0Xh8Wg5Zf+f7O5EZTBfawcDrolyMBkeT"
        "NJDtDQP0UAiRr+SFKFTeUW+P+m2Ia3L+sNhN4ci82sJc5gejpUxPjXHsseCL1lr+NmVBXnxHJzK/CpX2+FXD9OEYOj"
        "CKgbkUESnHALnDQ8zffz83x71gnhFnALOgvnTQPqt0MDbaIE7RKUEp30oyw/3kKoesmty+68qlQAbIskpL8f/P+3As"
        "nyZSAEq4mOCmhCMEkyvQJM0VBoslZuso4XLhThDCEaTrO+tQurg0SbpxR0eI4qBU5m1rnHVsgp5OeqDU47N8INCbqf"
        "QTdCEO18e88Ch61x2LdnHSbxhPz2TvMGOncDOhR8/z2SCkKE/in8bzZg/f0RmoG+f7sLo+8s8v/UM89sevypp5bMnT"
        "3nj3B3NrReOqBahfFS1RrM8UvnsmE31qoa1yzHgjF3FPhUmmcK9x+iK/xuwsLrPpP3Ol5vf79duGj3N6T3P+1QLPK7"
        "Fzvty0Wb2QdeGnUITndSlx8K+bF2YT3WSUJOB+E81sm5nFBfQQiSKiDknNDij09OsNGxMbZheOMEIIHXX3jpb/7p0c"
        "dXjJQKYIsrgqcf2nO33S4eGx8fBCSwO8j3LBT8WqUqhV8qgEolMBS0oAe/CIToHLkRQaVAH8y2ocoKtMhM/MgRcF/J"
        "eELtvy9fEThKIfP+wtfQ6kpfEIuEvUiAWC6LztqX5eYQdm0Fv62Pz6Yh+Mwp9mmCvw+Cz55es/qGh5Y/9slfXnHZJd"
        "urvOx0CgC3FU892YD98t3mzb92dHzsVZB51Qc/TozNQyEGK5UBNmUMWXnf8uYKWp4FDQhfnhIIC1rROLL86xyk4c+5"
        "EznzC3LRQA6q6TRExzpM5snLICziFgrOsdza/WmE89rWIoT7BGJNytoN69dBncovJyYn33Xx7664c3uWlZ1SARBF8D"
        "TArq/PmzO3f3xi/DhaNowoAJWAaDutJ1+AskLkw+2sFQ1dK9oohU7RQKG70YlbEEAD7rGYYkZevpLIrRpsU0eQteTM"
        "ibm3T9ntIBuwsPow3FUKof/ExCRbdv99qx9Z8dgp5//6ou/c/cB99e1dRnZqBaC33RcsuHZkdGwDzGXfHfaFKTHTUj"
        "MEOBkfLVTiEDN93p3KwgJ+oFhpFPnhBROGCqF6vvBnvJA8FyHjzhQrgnxm3hX0ThtvZgU/vwV3+1LeDnL128D59H6S"
        "KegxLcLUrollGeNvpXH+laufYfc/8vCnnnh65dt/dsmvV+wosrFLKAD4UQRwAzcvnD//EuAGjoRIwVwIy9RaKiEr5Q"
        "NsXzfd0ln3hEsKqrxyE4oyo8ayboEo5Ao6hPsZwS8Yb9YG8meVjntNJyW7HSGDHMEXHQm+KGwikiry9nA/yRFuE0LO"
        "7G5UCSv7WmBExibG2eMrVy5b/uQTr314+fJfXnrt1ZO7zHCWHXU77oijPtzT3X3u/Llze+fPmcvmzZ7DhgYHgSCsyu"
        "Ei6egwLoeN6IEOaWguUmG99Ng+7u55j+tzTIXd5LQiPWVWZ/Rx9755PXqOqRCiKkLSYUPGuJs1yG0ugX0P7nXu6zPz"
        "3kKvywqgfm7rLTa9hh2hCsP2GX4dVOiZZh1prV6SqHz9Nm28THEPURrDIyPNtevXf+7O++49/7fXXfvoLjedaQdXAs"
        "AJRlcODc46Yd6cOQyUAZs7ezbrrnWZycE8stNcMgKvphDJYGJEBFb+TWRj+eTYPu7t5u+4I+D2OXhYSUxBETBPKbQT"
        "/qwiyO8EFI7hb16nHlbUbIMVCDYTFsUxkenU21bQyXPYbsK2CzDeIuQfHR+/5pY7ln734t9d+Qu2q45n29G3ow45dL"
        "C3p/fYrmr1h5A/sFAqgaHZrK+3N50wrCx9HBElELWx/hERYO84HUiqBCqK1ERZiQUy18pHleA6z8mLlYMRbk8pcNXV"
        "uBAdaCWQozhyhZ91WJ3XppceFe6krQWngprI10m8ZjDthD00uCMh7cXxtmVcg1QZDG/ahC7lbwBBvvubP/yvYbYrz2"
        "fcWbZjDjv8iL6e3g8N9g98CNBAhC7BYH+/GTOuXYJIuwTqMQv3o1zoH1QUUQA5mHORLDziQRThIwn/HA9cR4XdVQht"
        "lYWnKBhjuVaftfXliaB1AtEZaa/NaG/9xLTgTkSxdaexefqcSRI47/TrV4U8+BoYOVLdfNasW79x9do1HwF2/6rb7l"
        "62hu3qA1p3tu34I48+Y6Cv78w5Q7P3XQBoYBbwApgzwA0vkApbTEeMRzygDFguSjBWfYq8gftY5Ah/pCB7FDinFYA+"
        "xzhzXY0gusgiBkYQACvqvOz444mJpjgDMvKsfELCeUlq1TWcz/fTQxaevLZWIEkYCVifXsF9JfCUEKzXJ9n6jcPn33"
        "zH0u8tuWPpDayc0Lzzbi86/MjndHd1fWbWwMB7kSCcMzTEerq6M0jAQQPKNbCKIHJ9+qBAh6341BTBNM7lIY8Onico"
        "7Iltf8XoMAzvXHhqTpIZqFEI/Z18e6kdjDXPKBoi4KEpPWZSUGInBiWkp4T2+8HXf+D+Rx76MSDEf4XYfpOVI9p3/u"
        "0lRx+DpS+f7Ovp+Ty4A93oEvT29sixzpHy5alC0KPJY67GlPvEYVQsYFHGum85ZZB7vkAZMFqJ6AtTB0RbHtzuXODD"
        "MJ4KfKoA8t0C7dMnHpNPLb09h1V8zYlVa9Ysg5DxO8676OePsJ14bHu55WxHLzrsTf09vZ+cPWvoGCQIwT1I57oT6G"
        "+VAXETKFLQ6EDCb0Xo8U4Vght2LBLuaQl96JoQgRlCAEFY7d5nylKLDoQ+KVIW2jVIpqhQtKXPifdLwVcCr90AjPOP"
        "wbZ+ePgLIPj/urOv8VIBtNmg3disrlrtU+ASnDFv9tyu2YOzZD0BRQIoLDFRBpyiBM5dEjFyuYHI99lJBMAIYVQM56"
        "OQssAf13stx+f3btsrCGYyJDOlrx1acT+m7pByLDRMo42wJ24kIAll7wkt2In3WNorQtbtKwWAqeIbhodvhoKxV/77"
        "BT8e3hXWd6kAOo8UvLmvt+/jQwMDL8Z8gS7IFzBkICEFfQUQO5EDG0KMlTLgQUIwqxQiNsWwo1Y4JuxYcC5DKnIPeT"
        "AHAXQO28kkXpVmK3JJufaKxUniCfn3QX8+X+Ap/IcU8fVQJv7hh1cs/93lv79mw66yrksFwKaUPDQIgvDd2bNmvQrc"
        "gjm9PT2uEnAIQps/QKMFvlvgkomdkIY5kD6EHPxzQcY/UiFDH0X4ioF1CNvdnnhuCK+I1Cseq50H900bbjMUhgh+y/"
        "r0Lc30E+FH+N+CpB74cD9Zs27td/7vsksW72prulQA0wsXHlGrVX87d2jOvIH+vrTBiPL9Y1/IAwrA5xBoaJGTfIM8"
        "Yc8ghE6JQR8F5IQkQ8qHcdYGzjOTQNNZyC5pn8mXEyGgQq8tfMsT+FQh6Gta1t/XLeNwSGe9wdasX/9raBzzxl/+9r"
        "JkV1zLpQKY5nbsEUd2Q47AJwAFfAHQQMoLEASQCn/swP0QYaiF3VcAEU0pNolD0RSiCTMbdmQ6CShJOku8IcKbJeZo"
        "qM5N6snmDZB4fR6Z52TsBZj9wP2R0dEVQOi+ERp23AV9+pq76jouFcBmbNCJuAYE4SHdXd0/HOjrf0F3Vy0V+oBbEH"
        "tZhHEmjyAbSYgjmlNgcwsYa48SihVFNrrQViEw1sb3L8jQS2gmYNI+CpBQhaDba7thOivU5L6y8K1geC9tDgtVoC0I"
        "557z+MqnfvSHW25+aFdfw6UCmBmC8FmVuPIrqCh8LiCCKs0TiCML902egHYVMuHETkOLPhFoWf/pKYRwhqGTC8BY2M"
        "/Pg/ie756N2YsMa0//vuX49jZMZyC9TtttqWEwGh206DkL91H44f3es3HTprOv+MPvLyhXbakAZloJvBuyxc6ApX2U"
        "zhfQwptHFGYFPppyaLFI6CNSXyALj3gUDC061+aEHRljbeB8cVgwMTyBCBftaAsufNjuW/jEknpCtX0nx9Tqt4j/Dw"
        "k9X4VeEF+7ZvGNT5Wrle2EbcG38vbio184HwT+hUAAvg6KiE6GyMBuUEjUBVWFbNl9f8J2ZNCRuOq4A7Hn72eE388y"
        "DOQPxBQReERie/IwXE8Q5RUrEeIwqADaJuIUwX2axkuFXoQtPk3aaXnHjjJoGbZfMf9LIL7/fSD6/heEX5Qrt0QAbH"
        "o1Akf0g58/f7JRP232wKxjIRdgHpQNH7Vw3ny22/z5bOHceQz7CkAhkWwHfRcogZ9dcrFcjFHsWX6SI+BY+4xCyNYe"
        "hAqRHJeBEod8qqRh5FYbkqiBdQGS4ni/z9iH3IXEq7OnsL5lj40VJwU6LXPcIsx/YobCEvSwAa67Dj7jBy+/7to15Q"
        "ouFcD0LP1RL8RMwE8PzRp8fm9376sXzpsHAr9ACvwCKfzzGDzOcAZBvV6HFlETbFzt9z70ALv9nrvZIyuWOwIf6ZoC"
        "R8hjct4NH8aaWFRw3ucPQnwCN7UJvONKxSLS0G25lW/lXf8+cbL1XKFvGUjfosk6jpBruE9Cey17bauVOBwBIf8mYG"
        "WffPWNN1xfruDSBZiapT/siDnd3d2v7+3ufjkQem9ZMHcehzqAbmgxztDao9APDQ4waCQiF9vk5CTbsGlYCvwE9IdD"
        "BQDtoOVgCHzs0Oe/4McrV61qDI9sOg6E64AUDXhW3skf4MHsQl8xxJFHDIb+nrdvZGKLlXSDknB/ARYg7+z9JMMJJI"
        "6CoD65pwASOslZwX+awKOFXCSu/+/4+tYVgDf0dVCm//T7m28aL1dziQDabkcefOgsgPLPRcs+OVn/MkD7uf19fc/f"
        "Haz8AngMLT369eDjy6Eisv0z1IePG0s/bo5BEQjoK3jLA48+jGgAxkAny9asX3f7T39zcetYKDOGxfpjELZFIGRdDj"
        "kYe25BRkHwoELwQ4uFHILT2aiNMmBWKUQquhC07sIrAXYsvxX2lifwqQ8fsvitbOzeQPyMlVdDYE14cAXc/gK+k0/f"
        "tPTWsVK0SwWQu73smGN7Bvv6ayNjo9+cPTS0e293z0ka2i9AaA+Vf2jtsTUYZvk1YZFRQR9Xlh5YZVFv1EcfeOQR1t"
        "XV9ZVn1qx++AcX/PjHrLgN2Rux1BgE9WAQxgoIbXes3QKaJxDHQd6gKILgti7rJNdA9TzUlYoFRKCT2BOowdfx+qLk"
        "nGCyjkPeJQEhT0xsv0X4AjgGcJGMpp2dxbfhLZwHCT33liJdKoA8S98PvvxHkbAD4fooZO/tS608Qvu50PwDmoHIRS"
        "+hvBL4MWLpQejZI48vZ/29fT+4/5FHlv/Pz396znTf0+EHHXw4vNbbwcfHMUWfcN2B2HUPuEIKNBoQUBzh0CJvG1nI"
        "VA565cch1t8W4Cjo7mXqBRNyFEtPQ3Qtau19iE/GvKtY/l3wMr+F+xMwfeezpQiXCqCIwDsEIP0+MLzhs3NnDe0OMH"
        "7PhcrKo9DPnzeXARKAyr6aHOgIFWHgvyuhH0+FfgQY/ZWrnsFrfnv/ow8/+vznHPDF65bczMDaP3X9H5dsdgrp6096"
        "5Sz4EV5SbzbfD2jjTRhB0Isd58qnQh8r6x57ZGJIOdAEJEw+4lnkYHILXGXCSZESJQ8RHfhFOW0ba3hxeFqg0/KIOw"
        "Pv6Wh3OA+veTu81pNS8Jn4DryTe0F5jCy9Z9m6UnRLBcCy+flHLQQr3gdC++X5s+f09Pf3HwT3905hPQg9WPv5cIuJ"
        "OrjIcbHhYAck7fB2HKw7tIDCwY4A7RuPPvb44/ftvnDht69bshiKRtZdddNtt85ozvgbX/mqfrj5PgjgaRFh+lGY8b"
        "2hAkAhfPLpp+VjKCCYTRPHNpIQe6nHcYhc5GE+Af+W01RlmrpMUpBpIVA+rG8Rfz3Lzjs+PIX0aox7Opqcy+NZA4Py"
        "WthuAcX7TvV3DSjTfbwU2TIKULQdM1Gv/zUI/yswJp/2+wehn62Oocff4MCAXOQo9DA4VEJ6tPZjeIxE3sYNbOndd1"
        "/4nxee/44trn05Pw+E8A1VNacwK8CpAC6YO18er9+4ETLa6vLckyufZuNARpqogEEKUa5CiA0ZmOUTtDKwuQlaeXAl"
        "mFmhd0g4j413QnNa4EmefksJ/hAIO9RSyPcPiVU+J3A0XP8wS3MQ8PY5pciWCKBdlV4VFvkx0M/v/dDF57g5s4YOlM"
        "pg9lxQBqkSQFZ/DrD6kL8PsH9SE3pSIUiCb3yiAe7AVbDw3/meM0/fIp1h3vaa1x4Jz389vIfuSiWWU4kySiAUElQR"
        "A6ZmCqzbsIE9vXq1tLwSKZC/zyoDm3+QVQK2VNl/THhdco2gi8QpvmkFj1smSQczI7GjEj6+/957Y8cw27LLgf+UK2"
        "jJ54JhHAIe//ivf3flt0qxLRVAR9srjn/xvtC5562gDD4AyuC5KPzz56QZe9joE/v8pSPBKhJuj0o0MC6VAB6Dcri7"
        "2Wx9Exbgpaf97V/PWA75O059/UIQ/jtA8HdDJYSCj+XEGHGoxHFQMGmyEIXt+hz66TCqSj52z4P3y8+RopzxAoWQ7z"
        "pQxCBIvX2LZOD5EN8XeBR2FO69dttdwnpUPkiytggXkCECk6xSaUBPfpzGA8dPgDI68ZdXXP5AKbqlAuh4O+HY43eH"
        "SS4nDfT2vRZcgFNh+k83KgEM9yEykCm8gAhq1RpBBGOpawDKAJJ9bq83G/8NX9Z/v+OMj25WjPm0N7ypAn78p0DAPo"
        "eKB8eUS8GHW33fiQIoTiDmHjQP1hVwEj3g2N+Owew66TYsvv02eI4YrHZLdQcKKYAsQqDw3yHpPIHXkQJUqAc+69ny"
        "un322FMWAPkxfJvsU8D8y7TgdPJuUykAnOjcajV/BAjozy+87DdJKb6lApjyduoJJy2C+P47Bvv7ToFQ4KHzCD+Qzg"
        "GYLa1Us9lI+YGJVAlAo1jI7pt8ChbiuW8//a++Mt3Xf88b3/xKEKzfouWXQo+3VasE0sc9JJAT0jPEHSHtcguN1N/B"
        "RBuIbIwymJbMYKKtcStiojho6jEiCyvA1rprCw55DVLwn7PvftK1cir0All7jnVPAqm8LatgtOCnSkC26pbHcO0//u"
        "zSX3+pFN9SAUx7e/upr5sDFve1kNL7V1Dkc8x8NSBUKgTYcTH3dHepSMGEIguleyBAETwOC/TzsBgve8cZH3m609d8"
        "/1ve9iywlL8BAXu+sf4KAVg0YB9LOQEkAmOnt0Ds1AkQy11UWUjKivFH1yFPRDlX33SDvH75k08qktEiAaH8cPTf99"
        "l9TyngqCiPOmSRfBwapcpcgFbiJfN45GBeck9edh8V/oZSAPoYvvv7ICZx0vkXX/REKcKlAtis7a2vfu283p7uI0ER"
        "vA4UwZshV2ABKgDpHkjXYEiy001YmBMGDYzLWwgVXgNP8SFYuI+94S//ohCSfvDt7+JgKb8AbPc/WSFXKEBafK0Q0m"
        "MdGZC702g0B/6H0oAzjUZSi86CRbFCKgB0gR587FF274MPSGUBeQ/s2WDdcWoyQnr9x+kwzmz6bouQd9n6/EBOgMjz"
        "+S38l0LfxMcb5PHW4h//6hfHliJcKoAZ29735rc+D7iCD8IosDNl+FCThSqKgNOBEO5qNCCVAdzCAv02LMqvgBJYnv"
        "fcH3rHae8CIfyJ4+87sN8KvYsG4vBEIq/vYH5BUOR0EWKMyr8I6YGcM4FHVFpwURpvVhG0nL/xyUUK+aXFz3EDYJ8E"
        "gvFN//uLCy8rV26pAGZse++b3hKBtQPEWz0Bogdn9Pf1v1IShip8iDMBkOjCbdxxDSbq0G/uPFig//G6D71/CX3Ov3"
        "znuxeBNb0VQn0xFXqfBKRCX9XH6pxfMORHAiw64E4tgIX93BFmUSzb4esC16YTe5KMD58kofx+Utrbcpl/6vNryN8y"
        "x+pxvKah7qfXXwYv/7b/uvCC0XLllgpgxre/etd7BiET7UgQ3LOxAQiEEp8zV7oH86QiwBHiXCYV1VWBEGYTTqwCP/"
        "pKsE7nvuYv3rP0o+9+3zy45kcgjK+qEL+/GoeEP3bPUdcgjr2Mvbyeg36PgCj3RxYdmH5R9JfCKoGWX8GXhAt8MpmD"
        "Bva7jL9j8c1jeL9h0IEMDSbJt//jpz85vVytpQLYotuZH/jw/pCx9g6o+jsLXIIahBK7THYhKAIUOplSrFwD4AvGgC"
        "P4xZXX/+GPsMC/KYXZsfx438b+8dhyAeRcQAlkw375BUAa9nvYvdjwU0EXnV3nNPcI8QG+ItDNOwOhPnOfEH9NTxFo"
        "bgCueRxIyDd9//zzbi1XaakAtsr2qY99/HgIJf41uAhvl+HDuXMlIsDEFxRcbBKCiOCRxx9nf7hlsRRGKdBECTjMv8"
        "8H4HE1gBJU0lDcScuwKPIIP9EBCrDKoTMPwT2THbFN0YCvGJIU5lO/PoMCiMWX5xqugrB/99B3zvvhn5Urc+pbXH4F"
        "U9+gCnDFCxcdfgkszguhCche4P+PQcef3TFciMQYEIkMaAR2+913yew8TPPFlmF4W0NFAMc1+Zja1XlzzjxWlUqCXi"
        "OfQz0u3YWq2vF+1f5NmlAU20hCHJFjFWI0UQay51wbB68NXOekHac1CjQT0fY+iIJjyZnzGFNTibhsTMJYdpy5Gl0+"
        "ePShh61ccsftS8vVWSKArb594RP/sAckD726q1o7C8KIz5oLrgGWEN//yMMksSdA+hFfP2TtXR4gzuQI+A1CaYiwEx"
        "MuCqIAba/L4QtouTBt8OlnEbrW3nMDMucarjvQyoYI4RhyA9gJ5/7XD1aWK7JUANtk+5e//WQMQv5xcA8OhBTcD+Ni"
        "r1biTIKPJQLzz2WiBSjwjqKoqApAW8evc/d5h4BfFLD/wXui+FrhhAc92E8UQG6oj5B7vpD750g4kPAFrf/86n9+/0"
        "PlSiwVwDbbzvrI6QeBBb4CLPYevmBXCy18QCFU4uz15n5sOAHKBeSLZWHYv5D+b8sKBAIIQmTZf0v4tQI+f1bgWzkW"
        "X5OAAfIQoozJ6f/279/9XrkSSwWw1bfPnP43ERi/c8ESn2Ggvcf0OwKvEn8qgeSfoMBnzisloEm/Tog7QusXs/uiA6"
        "QQcBKETwq2TKJPwwiuFeCWH+oLWXrK/hOL76KAlDAEt2MZvPQJ53z3m+UsAFa2Bd/K2pR/MK6A8MehHP+sJTdknT4u"
        "svZU+AkC0H8/HU0uREeBwIzi6MhpEFoJVIzld+cOMJXMxKUZssReZEnAiBwzMshUJTuppirkMcaavHUwoI3Xw6n/Kl"
        "dkiQC22vb5v/27hbAELwHBPDKUxJOJ88dhXz+uELRAFIBFC+TvFPw3pB8h/7aXH1a3EXOgfiDZx80EpC4CDQM2vZCh"
        "mxREyMMJKGI65fPf/Np15cpkZRhwa2yvOPb4C0EwX1oloTgnnKdCeMHQHjmukDCfCemp8xX1nFoB6DAYlfjtUaNHvu"
        "VnPDuanLFAWFCFAZn+O5Zzzh9lzitw03/Ci477zbWLb2qWq7N0Abbo9q+fPOvtAFePpam8Mc3nD1h+Cvnj2LXy/t9p"
        "9l+iA9W7TyiozTvK1NuWuDKdKoTvWSutrJATyB+aSsSZqnEI7TnnmvwtgDweQl62XKElAtii28kvfumNILRDaLGN9a"
        "64yTv0nFYA5pogInBvU7IvNlCfz5Q3x7eSh6j4BjPFmFpzplEBMyXLGty4HICT/MPMf1RZuI/tfuJxL77i6huvX1uu"
        "0hIBzPj25bM+0weL7AKw2rNCTH81k+/fKdOv0UDF8fOFtKSUlecp4aYeNPF/rijJjgRz2ienJv9eOEGiAR2+5Nz0LW"
        "gqWK8f47xpZhSYW07+Dp+j2SSTjFWZdBOfiz8bOIKL4AmfX67WEgHM+HbKS19+LizkdxtrLtN4PV+fnLMW3ab0ViqV"
        "LC9gogO2A3DGKndgucVWo4t5R9Zf/6v1gLb4ZmqxQgE2KqB1mW/xKTKw3IBGDpHGFCpNGBDaI1def92ycsWWCmDGtq"
        "9/5vNHgeX/LAjroBFkB/ZXGCUEHbhPrqlUfLifIgQ9kKOtfHHPyvKA6PPtIRgkCAAgx9yz7lTIuZf7r96qbGpqAh8e"
        "V8DssVIQFdj3e9VLX37+b6+7tl6u3NIFmBnNGcfng/XfK6blvYEEH+0C+NeEYv+xZvbzYvQa48tb546xqEJwI2SmGF"
        "DwNuIutixCEG6acCgPAUUVvwMnrk/zAAhRGIFb0Iy4GmjqzjRsGpeBmXPgChwBrsC58DJlmnCJADZv+86/nBOd+vIT"
        "AfpXTgZrHeWF+TB0V6vkhf/80F8K93W4ixE/vmMp4+1P8Bkx/HzaJGA7JYBX6JbladIQc0m/YLiQBc+xzDl+4Ktffs"
        "Kjl1179d3lKi4VwLS317/ilXsAyXShI/wVwvRXsr5+RviJq5Bm8fF8weKszbnOhVO0e74tnxVklYCTkuwd4zuMbJ4A"
        "8yE/IxECP0pAbpnzGKvBA/u/9sSTL7jkmqtKV6B0Aaa+/eCcf9sTFhT09E/HeDm9+9rk6ztVfqqclyuMLnQw34H2Of"
        "Bf3wkkAGgLSgV++0sMsv5/SAkI4jPo3AFmyEJOogZuanDEs7kFTKUak3OHQ2HS6+AFflKu5nSLyq9gCtoyrrwBhPig"
        "qmragZOErIUnDT6qlgCU1+jMQMUPyMIdYSfuZnYlJO7jzJxj9DFmr2fkGiNQ5Dk1Ia8fS8Utb98Sgk/es9AC7x4zco"
        "3+F4udKpRUrVq0VTOuls210N85zcSsqR1+w+/995e+dmS5mksXYErb/3z53FdDIs4PQIBrPtOvO/n4TH+NhAErSvC5"
        "iXN1yvATH17dFx0B/vZUn9jqycPU+mfDg0YJmFMWFejU30iHDLkP+ZkTSnTCh24Kchec6X7TK1912UVX/rZVugDl1n"
        "Y772vf7IblcyZYor5sww6StBPs7KMTeciiDuH6DuC/MDHvTkp027gARa/HtkD+QFDw7YMZwXfyhqziQEgP36pbNeiH"
        "DDlJGHIURKQjBO8FV+B+eOgcVlYDllvR9uOvfWsAvqVfg4C/zOb655Tn+qO9ZN4+Sd31bw3r794aP54mxxTcZsFC+D"
        "HuIQteQDTyLWP/M36+qwQK8gUC3AG2HjONQ3K6CTn9BWj1YdK6F1yPU9/18Y89WiKAcsv3kSqV44FEelm4XVegfj+2"
        "GXzpQuVtrH72jIG88LcdEYRtCb/816TP4BOIbKspgeyxI/gWOjhKIM0diLMEIZmEFDlIARFA2peg2eTPh2Khn8FTHV"
        "1yAOUW3H72re8fAYvp/8Df78tk8jnHFSd9N2hCeUFMv61vz6dnmnknHACbvtDzqRcEtBX8gLDnKQQTMmS0ToBnUoOZ"
        "xw2QoqLZb3v1qX+CUeP3sTIKUG6BbL8Pg2AvsBV7bltuyvhXVFceh7E3jL7L8LMQu69YebxJWM7feux/4j1v4l2X5E"
        "UZMhGHwHvu5L+2z8/c3Wf5fcZfMCfCQSMHjHnRERrlUGhAZ1e6UZc0KlAzkRun5Xov/M3HL/r+f8WlC1BuzvbL7/3n"
        "GUD6fciv4EsXme3WQyv1DDvnlOWFW2pyEsoPOwntCUIuUYN9Pc5snwCbKsDtfUOscZsqLLxXNP/MBA8gMiQmyyX73G"
        "MHCQSO85CE03eAQH5DAmrXQOUHNKPopcALfBtOf6QkActNbhf/4H8OhEVyNSykPTOTeXRzDtPcooDky5B+NFXVzWwz"
        "pB7nFtbmkX+EIHQLBEPdgSihGAorkiu5r15mfoVMR9g7IxBF5jX09KFw92GHKFwLCvzdp37gvb8tFcAuvl363+fFsH"
        "D+G4T+vZnW3bI3f8UZtW1uiaDTHn3Bxynbz1kbpZGnCJijSKasAJw/7URJzMRyyhP8NqnBGSUgChWK8xpwix2JtdC3"
        "Qp2GW7In4RL4fV5yyvtPq5cuANul46J/BxD/vdlUXjXOyluUjqQoN0CoFlhc5b5nIH4mju9X9hWw9tS9IOnAEv5zax"
        "GNO6Aey7gD5k95/jWMVhfmfF+8cxqxKKQXzAsouGYqLgS6aejz421TFRWYJiS24cgLQfG/BU6dXyKAXXS7/Ic/eSMs"
        "ip+CsNeq3jBOO7eOssrUUnIX0vv3vWsKbw0y8BFCADFMAcJPDzHkPbZZncHC8F20UQgdCH5GCdAiJEWMms7EHgoAhP"
        "AkKO+TXvHut/+pVAC72HbVeT+dCzeXgcAfbQg/NXrbClMOxDehJSqMxTyAA+U7VgS0XJhnUncyCoBnf+pgclChUnBD"
        "kJubLjSTVr5jwfeOhRpZnuEGpCuQfA++/zNe9s43N0sXYBfawPKfCTH8o+24La8xB3fTWXkA/neUqutHCjIXB+A/uR"
        "VCC6Ug78O/b62tVQLCSrDoIGGItalG3Ix0oS1q5R2Ln51apKMm0i3w0obT2+ZHwBXAvIBvlghgF9muveDnbwWf8AIQ"
        "/liP2LIW3Y6lZqTghKbTtof0U48U+AjBv9ax6R1C+HYIoWM0wKe3kDKCWHBcXBMgwgVFQkztNdTf0LmFakjJHXDu1O"
        "Pf+vonSwSwk2/XX3jREKyB0yMcWs+VxXeKb7IsnFBUWcYotrP607hW5xj4FOGUS4A6frNTAwVTbUDameAHhD0g+FMR"
        "dorm/OeVUR2TO8BZg/NF4CL8CE6fWGYC7vzbYfCbHwwrYQMshjGaycZysvl0BluiFmE4sy6UdceK79PXYG42n1nARX"
        "0ERKiPQGhPgo8n3vO0yyzsKNPQyy5kTlYgI/0BaOiOfAdGcPUxM98dy8kKdI6d75jlPm9aaRiZ6UsQCTpqyUWXnlK6"
        "ALvQdsP//epQuHmrgvhYJHISTcjJVOcVQnoLmTth/zljhbkD/q1/PCWWP4Pk+Yy4DJ0tr3C9fzgJiFr8cB1AJxbfsf"
        "4BtyF0jC4BoIBL4c7rjnjdKUmpAHax7cb/u7gPvp1ZcDgES/1sJXB4/+XFGXptfHtPMRSGDImvn1UAPJOkk1UAoYGh"
        "HXIGIca/AyXRQYPgDgSfFaQAdy7s0xF8eqwGm3758FNP/vtSAZQbu+kXvx4AITtGLfznwc3HlCA+R7axDCoCZrvUOv"
        "fDiiCoEAK5BEEE0AYR5CqJaSmF6acPTy/3f+atfC6BmD7XE3CDLiESge9Z9JqTniwVQLkFt5t/eclH0q6zHEnVr0zF"
        "RfAFulNFkGelM6hgm7oJM6gE8qx8gNWfkrDbY2wM8g3y3Bcd+upXrCg5gHLreAPSCG+qSsCH4J8vKCF8A9wscLv95N"
        "UJuElFeUqkWDinqwxy0EBbZZCfeDS1moApCH6h9c/NEXgGji8mf/VtOHGfViWHvOrEZlkMVG4zvv3Tx8547T0P3P9r"
        "ZJlPPeEkNtDXJ9OL99lzL3nLgqSfl39QqAACj+Vcs22VBJuS4Hc0TCT795vgn7uI1f82/PsndfHoQaec8FC5IksFsF"
        "W3ww86+HAQrNvSCbiRFPruri521KGLWG9PDzv4gOey3RcslEUpsm24GYiRn1RUTPR1qAACY8Y7UgBticW8x3KUQFHa"
        "rgiX+U5MTspz8H02urq6vgh3/qR0wJoXnPyyq8pVx8pEILb9zMJQKag67ixkxtmd997L+vt62aMrlsNtP+vr7WV/tt"
        "+z2JyhIdYFsej5c+fKbjZ5iUJp7w7vPrnGuS+r/YiQkWpFigaEn4TE/IpD5r2eLS10X48+xgPdgcWUBH9icoLdfs/d"
        "8ntbvW4tu27JYjY2Ps4m6pOX33rXnf9cLrJSAWzH8i+WgU2/ABbyO/W6xo629Uad1etVVq825HG1UWXLn3icrVm/jv"
        "WDMli7YYNUCrMHB6WC0BOFthgWFFNrMx6+32GWYUDw0bKv37hRx+DZw6AYV65axSYmJtgY7Gs3rGfjIPRjoAzwWtyh"
        "sOeOcoWVCmC73sByNcANGHPqcmDHajSjBGoNVmuAIqiktw3Y0epplwHz1ft6eqXr0C4EmG0XHggdKoSQQQfELXCLiW"
        "Zm2JhWD1J44QVGRkfZ6PgYm6zXJaxfs24dCPu4PNaCPw73x+G7ECj0mMUob9NMRPh+/qNcYaUC2DHcAOICaCGoA6St"
        "o+A3FAqAfoN1EIY6pqPCY1VQCI1mqhBQOWDXYbdYKCvonIV6/7tzAJyAYo7yyJzLvEYBp+CFLKkiwc89DoI9WZ+Ugj"
        "4+MSkFHAU+UWnKeE1LpAKvrb0U+iQt3knIXm6lAmA7AN16Bkj9B8xIPmVNEe5OguDX6jXpClSrIPzgCqBC0Aqgrm6r"
        "UgHoPvgsqwSCdf68EBVslrIIKIRcIpIc6+EcjWZL7gj3k0QLuwgcC0fgDfwXyR1w3Wi5uEoFsCNs0HsKk03E/qaoha"
        "dFKg2JAlJXoFpNLb1RAJIfaKYKAI7jpho1xvLLk7PH2WlDYeEuUhg5z99GmfBsvjJM8mmlqEbtdeXy6F59qBSTli/w"
        "wkMC0vJfDu7V+nJplQpgu9+W3r2sfsTBh7waDn8Por9Q+QQp3JVcgBL6OgiCUgCaC5A79LXHWzl8hPYsyGkcGhZ8H4"
        "4HkENOtyCe+5zhhqJ5yoTJllxg/RtNI/RGGZj76U4bebqwv4UIQcBj4+XKYuVkoB1lW7nqmTV7LNhtPxDcoyNvkCUK"
        "RqwIP4T5lSh27mN7MvT/8TYta1VWUVirKMj90LEgllQIYlkLzjnHBJrbY/X8hqCjx/5zpsRdvdlQiKeeKj5QepNyTx"
        "+b9Hdzrd4lbzIM4b9Xl6uqRAA7FhXA+ScYFpkw9klhJgGmtfca9hs0QO5LF6BRlbdJnOSXFAdQQdg6b2mLH3YZZA6E"
        "QjX1pkIBINTa+tc14akfa9QJSWrchXWgUN5frqYSAexw21PPPN3aa/c9rsfSYhCJo3i6GUGONAKI9W1s4v8pCoiNwh"
        "DG8lu/WBjCTFiLbCw1uS5j/clzhaw/YePzkUYAUXhIAKF8QwuzQgBo4Y2VrzfUsXocIgUeKtgIpOEHltxx+8XlaipT"
        "gXfo7djDjxwGgR+Q02yjdKotZv5hvB/rBTAZqK8XbuEYE4LwcXwMeQC/mrBozLjfh6CorDg3byCDCopDfXnnUBGgQG"
        "PYLw0D1mW+g4z7wz45qUKC8v6EDBeOy5yA9D4ojFNuvO2PV5Srp3QBdgb1+0qwrb+CfYEcwIHJQToi0KiBBUTYnx7T"
        "kKAehpnpLWAKirKNTEN9ClwmP1CpOAVlkdes1I8UpLkPGubrz2ojAZMUGdT1fXQX6sOAHt4KivLKcuGULsBOsT2+8q"
        "kn9t1jr9tA3E4BwerXM+7VZGJnp24AXmdhefY2EVkXwLmlroJJvHFJPkPcUZfBOfZcBv/YcR9sCA/771syj7gCCuLX"
        "Gxbu62O4XQdhwb/4/ZLFl6546sly4ZQKYOfZYEE/tu+eey0GmX4HCHZVDw/VU24d4VfRAXQXCgWcpssSheBzBmFWX5"
        "CUWxp7L2D7iYC7x5SbSNRUnqYSbC8S0CACTxVCvT4BYcB3X33TDaXPXyqAnVYJPL7f/2/vyqOjrK74m+2byTLZV5JA"
        "JK4oENkCKiqWiiglVVo4xWJLseiprT0u7an/9C89Xeyp51jbc1zO0dPaerQVy+IGbqQKIZBAgmhIyMZkmUy2SWaSTN"
        "bp775vmW8mMyEhUUny3jmf33zLBPPy7n33/u7v3pud44PYb9CHBY2hYUDlMzWxGA2z219o9w9SBqHv6UN1oaHASYf/"
        "wisEuVvv8JidXn8MAhfgeQHyeQA8gM2HPi16V6wSgQHM9vE8IICbcRSqvvKQzjdWswXJfyY+wAWrB6s+eJj240HX43"
        "QfDhsOHIdgdEFmIX65IS30pxJ/hoLdAd3vDGvh2MH/HRa5/UIBzP6B/PbedWtu3CWnwvu/S3n+tFvqOQGS8tmsNLEI"
        "RuMDoFuwMgjtMBSp4WhoodILcQUmzxsgBcABQF0C1NCYQ1YQ2Pk/xjxsFytDuABzZtQ3OvoX5sx/B4JK/ICFTEn6Ce"
        "AARgUDMIaN/QeAPX8wMBfCFQg9+yOdw8X7/ROI9/vDuxMaB4Cz+4aCfP6BIPBvqBjf2fJe0ScusSqY4AHMtbH+xrUI"
        "BhjcJoUjQGXDOB8gWuYBRIMPYAzNB4hwnnBTkgn0LBzjHkTkCESoGQjFoub9U3zfp6UDB+L+eH4UiuLWAx8eGhQrQb"
        "gAc3Kg6McC7JgmtfXYoM78H1QyBLWMwLDtww1huQDj9ieIyCEwRCQBsQnE//VKQqU7D2rJP8MaDqD4/O0IEz4Npt+w"
        "WAXCAphzY9Nt6y0wv38Npt+9FovlGjLFqe4dCXuU1cbZgDI7MFqOBowH5EXoRDSmIck45ccjtiWbYEGRUOVALgAx/X"
        "zEBESVnwF+9ikMv2GZJARXAO89gp/5HKwAoQiEBTB3BgT9TxDsh62gA0uShdOCY2H6UxFMjpbrKgWZR0dDQL2JWAMs"
        "mCZ8sd9jk6kwFPhMhT9kFuCghgXQmb5tj41lwzzd2UT3n4ESiMGDp8SqEBbArB93b9hIYOyzAPoegNCbSPi5EsBhQR"
        "2A+sZGvltaJYnnBaj5AJF37WDkf1qEPtJ5vCIjIRmDRAKSMQCV3+/jpdAT4xJ0BCGFJQhfAQrjz4gGvLr30Pufi1Ui"
        "FMCsHN+/c5MNpv5vTSbzE1Zl16f21CTscAP4Z3IFahrqudAQIGiHVWDG/engAVzc93QKJiz4F946oPCfCvbRmXb79O"
        "RUHjUY0mEcOiVAFkMDgJBNb773tlACTIQBZ91AU5AnIei/iUK1X5tk5VV/6SAFILsCEhf6tOQU5u7p4YISLiV4vPDe"
        "aNjwYHAxEX3RTb8/uAhnOHZhZNZh5MIiGukHgk2KDSFPruS4QqGMSKVxCm+MYlQ/o8Wan21cdMWVB7+ormoXK0ZYAL"
        "NibL1rcwE4/R9BEKKw6xtI4EkoSCCoMjD/DDPfot2T4Zrj5afkqIAiOGPTgicX5pvc90LJRmPZg+HdA7nsCQk+7f6k"
        "4CDQcnFQHgkYlIuDhEQG1EQhsghgPbigYL792r7/VojVIxTAjB7bN999EwRoD4Q4VdLMftnfl4VfPquCLylKgZ6fb2"
        "piFZVfBnbOUBQ/UhQgUv0A7XshhTynjWocGCTI9HvmL7qWJzSRsA/qawGqVYE4SDgcKIceOFqAFezDj3r8X/ve8oqV"
        "JFyAGTd23L3lBpjwb9gkKcOmmP3y7h9A/vm1YhGo99V3EuPjWWe3m3l6vRETgfwRE4RCSm6PuT9959D04WGl8GlifA"
        "KLi7WzGFuUYvYbuDJQ3QA1JVorksL7JKrugMGOixWYxuT8RYsOlX/5xYhYUUyEAWfK+NGWrauxiPdDsJMsqslvNoc1"
        "+SWzzgpQLAIarvZ27tsjft4CJfFSWEAvlPCjmu+RuAHMvx6f1gSb/tPgWuisClIGDYhmENrPlRk6IxO2IWc4GrVSaE"
        "GFUPn1kPLMqJVEgyJ5YGRk2I4fe69YVcIFmAmCn4BFvcFoMr4omS32sH6+7qzHAtT7tCu2oW1WdX0tq6qtbXB7uu85"
        "fKy4bDr+/+4tvIeEKXpcl2KyhCJFUUBZ5eK/v8LNg6fPVtbGxca+mpuVk355bi7Lyshk0TZboDS4zuxXXQKtcKjyXH"
        "MZhob8UATABfw/eeU/r78jVplQAJfk2LX1B/E4vYCda6ukA/TkXT7UzzcHBF9/jV2vE00zKRT4ZU01RQOWI022bCbO"
        "x9qVBd+Kt8e9kbdgQdJliAJkZ2TAIrCGCH14ZSADg2ofgWE1m7AdLs/Ol15/7YBYbQIDuOTGisVL/w1BvoeH9XhoTy"
        "b5yH5+cNw/2O9XPuNMzTIbmhp5t9xGp3Nvb1/vc01O5+gMLX5SNy8948jw8NAOEJ9Mklli8XZ7SDjQEPD/OT6gnFWs"
        "wKBiBRwniMY+dhearx4r/byiXqw4oQAuifHg9h2xEP69EOK7VOHXBFsKCL18WJV78jPtfRy08xET8Fx9HWt2uf4JAs"
        "22o2WlIzM87fl8Ylz8WgCEeXIlZAuAwVgoAUkR/AAIqBN0jSMQAAcN6n0bfux9UALrV1y3ZD8UQZ9YgUIBfGPjoR0/"
        "TsSifAm7WqEeyZcUco/VYgmL/Afuy+9Sf7ymVicX/nqHo7Oru/vRI2UnHLNhjjLT0g4gMoCEp9GrzCYzV4JUCt2shT"
        "flnV5TBtrOzzSLQK8MjHI11fl4ev3KJUvfP15RLpqGCgXwtQu+oSD/+hQs2BfA1f9eUEgPfr2VfHtt97cGuQB6k5+U"
        "BAmAs93FamH21zQ09Ls9PTtRD3/WlMSGYvNlZ2Qegq+/GJdXEN5BYVGuBEwmHSNQDREaAq6B6iaMDOG+WXMTFIshDz"
        "9v5aql+W+vXJLvO15xyi9WJhNhQPb1tP0qxOJ8y2I2hwB5SqhvBHX9RnzMbLVzRRAMCAYAQFrgLW2t3PSno7W97W8Q"
        "/j2zbb4+PVHSccPyFduAC/TQ725CbgAlORHt2cgrH+EwGbVQoUm9Bn/BhFwCet9oktAxeZiHC+XQIQcIb4Xr1AYXYz"
        "f+mRfFyhQWwFc+frnz/vuwc72MHd8S8O0tGqef8/qRxCNFxcASMMv3NM6/RcMALFjUXT3dMPvrOerf2NJ8FKSfXc42"
        "16yskJOSlAR5HTmHuP4dUHwWEnS1AxLnBwRZAbimaslQAAZrNA6b5iKY1Od416TkEuDW7bDIvMWnyorFChUK4Csbj+"
        "7a/UMI/18gxLEqrVfSCbXe15cg9BJYcPwcwvajXdDb18dqHee58KOPYFFvf//WkvKTnbN17qDYyB2oyExL7wBJ6Fbs"
        "8hJZAbwMGpU+M+lwAOUwkJVkCgEEda6BQQMQjdRD7ZbVy5a7C5Yua4QiEPRhoQCmdzz+0wc3Y9G+CuGNUfP4iYpLBB"
        "baxaxWna+v9/m160DYj1JkiS1H4T6yAOD3b4OZXDkX5hFhztKs9IxWxPgLSQEgPVruhwirSQsFBtGFjTrfPxAx6PP5"
        "eC4BVVBS7hOFEm3E/RvXXL9839GTpT1i1QoFMB2Cn3PTylUPwe98EWa82WqVhbjb62FA6vnizUxN40w3SeH7W9Uzzw"
        "FQrhU3gEqA1zU6+M5PqH97Z+duFM3c19zaOmfmFMSgk95ebzzyE9aoO7s9JpYrUrVJipYyHPRZfpdGt6eHFZ8q5USh"
        "tJQUGTeQlUYqaG+FwBzePVJ6olOsYKEA2NQYbatWw+x/Bci1QQ3p9Xg87BgW34KcHHbt5VexhLh4DupR4g5xLhPscU"
        "quvyz09FmC4qDynudbmrnwE+rvbGt7Brf+gHj/nEKw6+D6pCYnl8MV2Ij9PI0wALKQ7LExvBKyKsyaMsBBPAkqmcYV"
        "Lf4GNpuVv3umqpKzCTNSUpWoArcQkoZHRtcfKT3+V7GC5WEUU3Bxg8x1ynCjRWmDuUlCXlJxkl22IJeBjIJKNylcwG"
        "sdDexwyVHO5pO40NtYlC1wUBSg3d1FDDl+NLtaG0D1fQE8/9G5OK8nKsqdmNvvIPJx2tHSAuZjMylEnkSkzl00MBR1"
        "/gj5r26oZR8cKeIuQHxsHLsqN4/dXHAD/+6Z6rMaFkNJVChKaherV1gAUx6Lr74mD4koO2QSi8R371SYnAVL8llKQh"
        "L37+neZ6UlbEX+MlgEV/I0WNUFUEt+dXR18feq6mqIIXfO29t757Hyk2fZ3O6a7J4/L2v/wODAeuzy6TTHNJ8JcXae"
        "Pi1bAXLmILlXCUiRrm1sYJXnqsmN4FwCohenJCez+iYHi4VFQMLv8faiJsHAz06crjgtVrBQAFMaVy+8PA957jt4qA"
        "q7EHxXlp2ZyeZnZvEd52xtDbCA42zdjWvZ8kWLWTLy4G1a2S85LOju8XCTv5oUQG0t6+3ruw0tws6I2WWEh/QkJSRG"
        "ozPwBrKSuBKAwqR6AhKnDMvzTuY91UjMzpzHWZNnqivZvLRMKIA4bp11ud38fQIGPb0ehqjKHhRUEQqACSLQlEY/6v"
        "VTsQuV20+gE9W4p6o3iGtzFt/agjVs+bWLWQLM0kD2n5mb/YRWk4nKTf+mRn+nu+s53KsSM6sf/mfhDqU2trQ8BuVp"
        "iYJ/T6HBLGQQms02ZoaPTwqAogY55kx2xy23cYvL0dLEy4xDoSKs2gsLIAYFVX247ufzLoZQAFMe5NOPINynVu4lBU"
        "BNPOgg4I92rEV5V7JklLwmc9+slPqiM6WzIpuPCz/MfubqaP/74ZLih8WsBo/ik2XUGOSJ29feYpGaLI8RBkAKgCwp"
        "8Ab4HJuHTZoimJeazvLm57JmYAe9/X08IkNCPxg/xK/p6BcKQCiA6RhoXHEQiykJJuqT8CvvR6cbiXZ3qtxL4BR1vi"
        "G3gCwCfaVfvM8otFd7vh7FPeqI9NMGBfC8mNFx5npk5PHGVud1oP5ukDhlWLaikFbMzwPGAR4NIOVLmAqFVLvxd0Ao"
        "lf8d6Iy/xfPoSPQUrDaHmFGBAUx5EFsP/rsPQvzO/KzsN9u7OqNB/slAtM9OQu90uVgcgCjyP6nuHpFWSAG4OjpYFa"
        "r6EEYAsk9rj9ezHTtdkZjR8cODiOlXokLwnfDr48zUJZnYguAH0OjqcfNQYLPLySprzsE983E+AH2vpc31If4Gm1Fk"
        "5BUUUemmv5sYQgFM6wBxpx0m/d7s9MzP4HMWwjKwtXW0Gynhx+BnSjOMAQ5EEVBFgB8pAHdP96aPjnz2sZjBC48mZ0"
        "tzRmraR3CftgEAjKLwH7la3d4ePGul56wBLlVV7TkGpeqHJdCO4qmPIK/id0fLTtRRpEUMoQDYV0xnbcRCezo5IdHd"
        "1tW5ELdSyOQnv5NM0X7fACX3cOGH7/+Bx+v9I/j+orItm3B4sDWLpxAPbkbM305+P5n8BKbiGa+ahF3f4fMN/P7Qp0"
        "WFKKFehueiLoBQAF+zImhuOoamnv+Af1oDvzMDVkEWVwKwAiDwzOFsOQB/dQuSUwQiNXl3oAWhwGugWJcRu88F/56E"
        "nw6Qh95EmG93SfmpPWKmhAL4RgfM+wFHc3MZqKj7AVBVwCddh644NixSL3alX8AsrRazdHFjXlr6J8BbssAOXAqAzw"
        "MQtRhZlDvhHvwJTMJWMUNMVAVml1xx0CXromxRP8fOdQDJQi+LGZnauHnVakRVzfcj/FpfVFIsyoJf5Pg/itHmRRpO"
        "lKkAAAAASUVORK5CYII="),
    16: (
        "iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAChUlEQVR4nIWS20+SARjG6a7ZXesv6LrDtK10XbRs67"
        "DW5jTTmUWBkhrKyVAIAcHDTCU/1IKWNkFNRMUDOPUzEFRQ8RsgCAvTzWatRqWredFmPU22WvPEc/luz2/P+z4vjbZD"
        "KZevMvKz6WQFX8hWSeTKZ8rqeUKmVMg4AmFORpbz+sVLybSDVEhnPHlRVYv2p40YbesENTgCW2cPups00FTWICcji7"
        "XLdObEKRo9LT2ZkCpkdWLpxyljPwIjVqw5KXz3h/FpzofQuAPO3kG01qicqVeuHdoFKcim36x+JNo0t+gwOeeHdYLC"
        "FyqAzcV3WPeGMG91weTwYFTfBUZ65uk9499Lu6W19w6CPhBAgz2Mr57FKGDDG0KHPYjUvkW4SRtKHjwU77kGn8lacQ"
        "0Mg2dwgdHp/pdgwxdCvdmDjHY3fFYHakVl07sAifEJR+Tc4l8OQx+8FhLLE058dvvwI7CEb95g9B5v30xGj0rIlOt7"
        "riDKLySMTdrfpN6AWZMFwbEJrE7NIWydAjU0CtvrHvRrW7cIqUK0b408JitVWsT7qZLI0a5qxNDLNnSpn0Mtq4CMww"
        "+Xc4uT9jWrJPLz5hZdj4TNSeExcrfkHAGkRTxI2Nzt/kMXziXF0WKpqbwyTldPrHosY4hQfkSoAD64KFha9VDLlHdi"
        "Akh9l3hheBzvp93RB4rMb0P8WHNRmDWZI9YO47EDATN95hsmTUvvZLcJIdKBJds0Vuwz2P7OIGnX+obHz8ZMkRifcJ"
        "TPZC3r6tUwNGpgbNaCfff+q5jGvyor5KZXCIQLBdn0Uh6TJS/NY6tqSh77SvPYx2OaczNvH25WVM02lJWf/H/eVkdw"
        "q4ViYqfhD+Nii1B1nyNpAAAAAElFTkSuQmCC"),
    24: (
        "iVBORw0KGgoAAAANSUhEUgAAABgAAAAYCAYAAADgdz34AAAEtUlEQVR42pVWa0wcVRQ+szOzMzu7szO7wC5doULLkv"
        "KqFhTRVCnUpqUoiEljYhNjfLQNaUx9pD98/NGYmP5o7I9qTdVE7UsbIiTiixartlZJECxLipEKlcY2C7vLss9hZnY8"
        "d6GEWHYLJzmZmztzv++ec+757lCQwe6vrslx5+b9mOtwdDkkuVO2SyMmimplWfZJwzBGdV0/4g8GYvFEvCUQCrWFZs"
        "JHz5z/+eT/cZhMBBaOX+stKq5A4Aqe4141s6xuE6y0bLcDgkM4Etlr4XmIJRIUbgDGJybOLYWTkUCwWNYUFRQCggJn"
        "NoMkiggukSdgBISACkdmYCYahXgiAcHpae+yCLbVN+Qg8Ebc5QselxtEmw1EK3HrwpiYJNohEpPQYxCNRUHTtUcjrW"
        "2uE11f+pckqKlcTxWvXn14Q3nlnuLCQso/FYDSNWuB5szA0yxQ+I3VIgBD02DgmMP5pMKAaBeBwXEZa5bGrk28gq/2"
        "LyYw3Rz0+y4ZvJnbp2rqR0Mjl8HjdkGKY8FnXwU9mhX0VAooCmnQCRltokHHUacmw6TLA6zFAnab2Lr1oU2wJAGxY5"
        "0dszzHP3/txo0RSZQACwBvD0WgstABIYq7Jb9XQYAHipxwaFQFVrJBntNZioX3ZiQg1tXzXT4WslSw8JAwKBgKKvDw"
        "91NwKXZrAfujFDT1huByxACW5yA/z0WiaM5aZCxm0x3ufBONudYCIdjlpEHmdfBiulKYJjxCC9/W2lLwYu4szutgRF"
        "VwSOlTth1fvZuRAI/nfQ5ZBl3TwZJMQrubB55LoUP6eBJ4UgpiFVYTlLAAyqwGijKbrgtZnzUCVVUHk0kFovEYpIwU"
        "upEGJkbKSwpNPKEkgXw390xCAj2eTJAoB7MSxJPJTyeDU2UOyb7XLtpNAu5MURQ8kuhcEiPhCdMcqDIPjI2GHU2efZ"
        "ja3YvxqEydvGfnUw05svwxdm8RkQcbaTZBACt2NiZrvsFiEI5GIBQOq5qmvXV90v/O+8c+UbMS3FN1FzRtaiwu93qb"
        "cUfren+54MIUtThlmUMHySamewJBYSoYUJHgIr7fd/rrrwaWJRWyJDEet7seNajhTk/ByYFhn+GU5B3SvMgFEdiCFR"
        "dIY2EKsTpvfvj5iYFMmciYopee3UWiaZueCZ8uKSqmUVkR2JJODyk6Ebk//75CfBRrVPX6wQPJFanp+nVlBOqZu8sr"
        "6UKPJ61DJpNpTi6InCOZgI7iVzJx/d83cOq1FUXQ89mp51AxjxJ5xksGWIZJn3MaSeYawUinbFZVwR8IqFjw6sadO3"
        "zLjsAqCDriHMfbaovdZnMREhLBYhJCgDKtYfeP4Z3Rgst8y47gptVtqGmvr607vL1hM+CtBkRCiJOFfX8MQs/5n17u"
        "+Lb7YKb1zO0ITCbqyF/jY1tRzlvIFWlmWGAY1Cnc/e/DQ92B6eChbOtvS1BdUbUxz5nz4Oj4WB8W2M8yrIiRUDRDuw"
        "ryV9ViaurO/XrxwoqPKbH9u9sfwevzC7z0+zu+6W7s/uHsQpc2N27mHtuy7Qxqz71X/rn69IEP3ju1ZAayERD9wb8L"
        "3+Dw8BOLwYl1955VfhsceNxsNg/oKV3NBPIfLEHlJM+ze9kAAAAASUVORK5CYII="),
    32: (
        "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"
        "7Bq7nvF/A2iYWzbJGZpvAAAAAElFTkSuQmCC"),
    48: (
        "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"
        "/A8at/bBB/UHCwAAAABJRU5ErkJggg=="),
    64: (
        "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")}


if __name__ == "__main__":
    main()
