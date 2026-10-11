#!/usr/bin/env python3
"""Tiny native attachment model: nonclosed support, core and rest failure."""
old = {'r', 'o'}
support = {'r'}
old_p = {'r'}
old_R = {('r', 'o')}
core = {'c'}
core_p = {'c'}
core_R = set()

assert any(x in support and y not in support for x, y in old_R)
# The attaching map sends r to c; its one-vertex image is
# relatively closed INSIDE the semi-closed core (no R tuple there).
assert not any(x in core and y not in core for x, y in core_R)

# The actual simultaneous attachment has two old copies, whose
# roots are identified with c and whose outputs stay private.
exterior = {(i, 'o') for i in (0, 1)}
whole = core | exterior
relations = core_R | {('c', (i, 'o')) for i in (0, 1)}
core_range = {'c'}
rest_of_copy_zero = whole - {(0, 'o')}

def relatively_closed(subset):
    return all(not (x in subset and y not in subset)
               for x, y in relations)

assert not relatively_closed(core_range)
assert not relatively_closed(rest_of_copy_zero)
assert len([y for x, y in relations if x == 'c']) == 2
assert core_p == core and not core_R

print('PASS: nonclosed attaching support, semi-closed core, induced attaching map')
print('PASS: entire core range and the copy-zero rest both fail relative closure')
print('PASS: actual whole attachment has two incompatible outputs at one root')
print('PASS: core contains no nonempty intrinsically U-closed test')
