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

opa = '''
opa:
  initials = 0;
  finals = 5;
  deltaPush =
    (0, (call pa), 6),
    (1, (han), 2),
    (2, (call pa), 6),
    (3, (call pb), 11),
    (4, (call perr), 28),
    (6, (call pc), (16 17)),
    (7, (call pd), 20),
    (8, (call pa), 6),
    (11, (han), 12),
    (12, (call pe), (24 26)),
    (13, (call perr), 28),
    (16, (call pa), 6),
    (17, (call pe), (24 26)),
    (20, (call pc), (16 17)),
    (21, (call pa), 6),
    (24, (exc), 5);
  deltaShift =
    (9, (ret pa), 10),
    (14, (ret pb), 15),
    (18, (ret pc), 19),
    (22, (ret pd), 23),
    (24, (exc), 25),
    (26, (ret pe), 27),
    (28, (ret perr), 29);
  deltaPop =
    (5, 24, 5),
    (10, 0, 1),
    (10, 2, 3),
    (15, 3, 5),
    (19, 6, 7),
    (19, 20, 21),
    (23, 7, (8 9)),
    (24, 12, 24),
    (24, 3, 24),
    (24, 17, 24),
    (24, 6, 24),
    (24, 0, 24),
    (24, 2, 24),
    (24, 8, 24),
    (24, 16, 24),
    (24, 21, 24),
    (25, 11, 13),
    (25, 1, 4),
    (27, 17, 18),
    (27, 12, 14),
    (29, 4, 5),
    (29, 13, 14);
'''

n = 11
for form in formulas:
    with open(str(n) + '-generic-larger.pomc', 'w') as f:
        f.write('prec = Mcall;\n\n')
        f.write('formulas = ' + form + ';\n')
        f.write(opa)
    n += 1

