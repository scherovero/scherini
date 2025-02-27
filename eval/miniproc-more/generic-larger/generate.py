#!/usr/bin/env python3

formulas = [
    "XNd perr",
    "PNd (PNd (call And (XNu exc)))",
    "PNd (han And (XNd (exc And (XBu call))))",
    "G (exc --> XBu call)",
    "T Ud exc",
    "PNd (PNd (T Ud exc))",
    "G ((call And pa And ((~ ret) Ud WRx)) --> XNu exc)",
    "PNd (PBu call)",
    "PNd (PNd (PNd (PBu call)))",
    "XNd (PNd (PBu call))",
    "G ((call And pa And (PNu exc Or XNu exc)) --> (PNu eb Or XNu eb))",
    "F (HNd pb)",
    "F (HBd pb)",
    "F (pa And (call HUd pc))",
    "F (pc And (call HSd pa))",
    "G ((pc And (XNu exc)) --> ((~ pa) HSd pb))",
    "G ((call And pb) --> (~ pc) HUu perr)",
    "F (HNu perr)",
    "F (HBu perr)",
    "F (pa And (call HUu pb))",
    "F (pb And (call HSu pa))",
    "G (call --> XNd ret)",
    "G (call --> Not (PNu exc))",
    "G ((call And pa) --> ~ (PNu exc Or XNu exc))",
    "G (exc --> ~ (PBu (call And pa) Or XBu (call And pa)))",
    "G ((call And pb And (call Sd (call And pa))) --> (PNu exc Or XNu exc))",
    "G (han --> XNu ret)",
    "T Uu exc",
    "PNd (PNd (T Uu exc))",
    "PNd (PNd (PNd (T Uu exc)))",
    "G (call And pc --> (T Uu (exc And XBd han)))",
    "call Ud (ret And perr)",
    "XNd (call And ((call Or exc) Su pb))",
    "PNd (PNd ((call Or exc) Uu ret))"]

n = 11
for form in formulas:
    with open(str(n) + '-generic-larger.pomc', 'w') as f:
        f.write('formulas = ' + form + ';\n')
        f.write('include = "../../Mcall.inc";\n\n')
        f.write('include = "program.inc";')
    n += 1

