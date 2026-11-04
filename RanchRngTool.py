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
Seed to RTC tab: date/time (RTC) to set so that the boot seed reaches a target seed within a range
of advances, on the emulator only. In Dolphin the boot seed is Origin Seed + 0x39EF8B0 * seconds
since 01/01/2000 00:00:00; the Origin Seed is kept in ranch_rng_tool.ini next to this script.
Trade Offset (Generator and Seed to RTC): when Phione and Mew are offered in the same deposit,
Hayley offers Phione first, and Mew's IVs are generated 62 rand() calls after the A press that
accepts that trade (Accepted) or 23 after the one that refuses it (Refused). With the option on, the
Generator lists the seed and advance of the A press next to the IVs generated that many calls
later, and Seed to RTC aims the A press that many calls before the Target Seed.
Seed from Camera tab: the current rand() state from a sequence of camera movements of the idle
ranch (3 calls per camera), after an Initial Seed or by bruteforce over all the states.
Seed from Dex tab: the current rand() state from the Pokédex descriptions that the trade shows at
every Yes -> No -> No loop (JPN Platinum or German EUR, 1 call per description), after an Initial
Seed.
Seed from Dice tab: the current rand() state from the faces of dice rolls (JPN Platinum only, 3
calls per roll or 5 after a 1, 5 or 6), after an Initial Seed or by bruteforce over all the states.

Only the Python standard library is needed (tkinter).
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
# both trades are offered in the same deposit (measured in the game).
TRADE_OFFSETS = {"Accepted": 62, "Refused": 23}
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
}


def keep_clean(field, variable, clean):
    """Rewrite `variable` with clean(text) after every change of `field` (typing, pasting,
    deleting or a value set by the program), keeping the text cursor by the same characters."""
    busy = False

    def on_change(*_):
        nonlocal busy
        text = variable.get()
        cleaned = clean(text)
        if busy or cleaned == text:
            return
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

    variable.trace_add("write", on_change)


def input_field(master, variable, kind, on_submit=None):
    """ttk.Entry for a value of `kind` (see input_width and FIELD_CLEANERS): sized for the widest
    value it accepts, and corrected while the user types or pastes."""
    field = ttk.Entry(master, textvariable=variable, width=input_width(kind))
    keep_clean(field, variable, FIELD_CLEANERS[kind])
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
        for sequence in ("<Control-a>", "<Control-A>"):
            body.bind(sequence, self._on_select_all)
        for sequence in ("<Control-c>", "<Control-C>"):
            body.bind(sequence, self._on_copy)
        aqua = self.tk.call("tk", "windowingsystem") == "aqua"
        body.bind("<Button-2>" if aqua else "<Button-3>", self._on_context_menu)

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
        notches = int(self._wheel_delta / 120)
        if notches:
            self._wheel_delta -= notches * 120
            self._scroll_by(-notches * self.WHEEL_LINES)
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
        try:
            self._context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            self._context_menu.grab_release()
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

class AppSettings:
    """Values remembered in ranch_rng_tool.ini, next to this script (made at the first launch)."""

    PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "ranch_rng_tool.ini")
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


# ------------------------------------------------------------------------------------------------
# Tabs
# ------------------------------------------------------------------------------------------------

class IvRangeFrame(ttk.LabelFrame):
    """Min/Max spinboxes for the six IVs. A click on a stat's name sets its range to 0-31 (any
    value), a Ctrl+click to 31-31. A right-click anywhere in the frame opens a menu that copies,
    pastes (as "0/0/0/0/0/0-31/31/31/31/31/31"), clears or maxes out all the ranges;
    on_message(text) shows a short confirmation."""

    def __init__(self, master, on_submit=None, on_message=None):
        super().__init__(master, text="IVs", padding=(10, 6))
        self._on_message = on_message
        ttk.Label(self, text="Min").grid(row=1, column=0, sticky="w", padx=(0, 6))
        ttk.Label(self, text="Max").grid(row=2, column=0, sticky="w", padx=(0, 6))
        self.min_vars, self.max_vars = [], []
        for column, name in enumerate(STAT_NAMES, start=1):
            label = ttk.Label(self, text=name, cursor="hand2")
            label.grid(row=0, column=column)
            # Tk runs the most specific binding: <Control-Button-1> when Ctrl is held
            label.bind("<Button-1>", lambda event, index=column - 1: self.set_range(index, 0, 31))
            label.bind("<Control-Button-1>",
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
        aqua = self.tk.call("tk", "windowingsystem") == "aqua"
        for widget in (self, *self.winfo_children()):
            if widget is not self.menu:
                widget.bind("<Button-2>" if aqua else "<Button-3>", self._show_menu)

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
        try:
            self.menu.tk_popup(event.x_root, event.y_root)
        finally:
            self.menu.grab_release()
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


TRADE_OFFSET_WIDTH = max(len(choice) for choice in TRADE_OFFSETS)     # drop-down width, characters


class TradeOffsetOption:
    """"Trade Offset" check box (on at start), gridded in `master` at (row, column), with the
    Accepted / Refused drop-down on its right; the drop-down is greyed out while the box is off."""

    def __init__(self, master, row, column, on_submit=None):
        self.enabled_var = tk.BooleanVar(value=True)
        self.choice_var = tk.StringVar(value=next(iter(TRADE_OFFSETS)))
        self.check = ttk.Checkbutton(master, text="Trade Offset", variable=self.enabled_var,
                                     command=self._sync_state)
        self.check.grid(row=row, column=column, sticky="w", padx=(16 if column else 0, 8), pady=4)
        self.combobox = ttk.Combobox(master, textvariable=self.choice_var,
                                     values=tuple(TRADE_OFFSETS), width=TRADE_OFFSET_WIDTH)
        self.combobox.grid(row=row, column=column + 1, sticky="ew", pady=4)
        if on_submit is not None:
            self.combobox.bind("<Return>", on_submit)
        self._sync_state()

    def _sync_state(self):
        self.combobox.configure(state="readonly" if self.enabled_var.get() else "disabled")

    def offset(self):
        """rand() calls between the shown seed and the IVs: 0 while the option is off."""
        return TRADE_OFFSETS[self.choice_var.get()] if self.enabled_var.get() else 0

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
        # Show the seeds as they were understood: 8 digits (the date is already complete).
        self.origin_var.set(f"{origin:08X}")
        self.target_var.set(f"{target:08X}")
        self._settings.origin_seed = origin
        return (origin, target, first_second, min_advances, max_advances, max_results,
                self.trade_offset.offset())

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
            "activeforeground": colors["menu_active_text"], "selectcolor": colors["menu_text"]}


def set_dark_title_bar(window, dark):
    """Ask Windows 10/11 for a dark or light title bar; nothing happens elsewhere."""
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
        # Check boxes and radio buttons keep the window colour on hover: only the indicator reacts.
        for name in ("TCheckbutton", "TRadiobutton"):
            style.configure(name, background=p["background"], foreground=p["text"],
                            indicatorbackground=p["surface"], indicatorforeground=p["text"],
                            upperbordercolor=p["border"], lowerbordercolor=p["border"])
            style.map(name, background=[("active", p["background"])],
                      foreground=[("disabled", p["muted"])],
                      indicatorbackground=[("pressed", p["pressed"]), ("active", p["hover"]),
                                           ("disabled", p["background"])])
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
        for sequence in ("<Control-c>", "<Control-C>"):
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

# The application icon: Mew (from Mew.png), as base64 PNGs of every size Windows may ask for at
# 100-200 % display scaling (16-24 px in the title bar, 32-64 px in the taskbar and Alt+Tab).
APP_ICONS = {
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


class RanchRngApp(tk.Tk):
    def __init__(self, settings=None):
        super().__init__()
        self.withdraw()                 # shown once its size is known
        self.settings = settings if settings is not None else AppSettings()
        self.title(APP_TITLE)
        # Mew as the icon of this window and of every dialog; Windows picks the size it needs.
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


if __name__ == "__main__":
    main()
