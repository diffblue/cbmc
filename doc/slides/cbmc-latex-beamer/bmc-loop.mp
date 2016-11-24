input rboxes

verbatimtex
  %&latex
  \documentclass{article}
  \usepackage{times}
  \begin{document}
  etex

rbox_radius := 3bp;

diamond_radius := 5bp;

beginfig(1)
  rboxit.unroll (btex $\matrix{\mathrm{Unroll}\cr\mathrm{transition~function}\cr k~\mathrm{times}}$  etex);
  rboxit.check (btex $\matrix{\mathrm{Check~for}\cr\mathrm{counterexample}}$ etex);
  rboxit.checkct (btex $\matrix{\mathrm{Compare~}k\mathrm{~to}\cr\mathrm{completeness}\cr\mathrm{threshold}}$ etex);
  rboxit.increase (btex $\matrix{\mathrm{Increase}\cr k~\mathrm{by~one}}$ etex);

  unroll.c = (0,2cm);
  check.c = (4cm,2cm);
  checkct.c = (4cm,0);
  increase.c = (0,0);
  
  unroll.se - unroll.nw = check.se -  check.nw = checkct.se - checkct.nw = increase.se - increase.nw;

  drawboxed (unroll, check, checkct, increase);
  
  pair diamok;
  diamok = ((xpart check.ne)+12pt,1cm);
  draw diamok+(0,diamond_radius)--diamok+(diamond_radius,0)--diamok+(0,-diamond_radius)--diamok+(-diamond_radius,0)--cycle;
 
  drawarrow (.5[unroll.nw,unroll.ne])..0.5[unroll.c,check.c] shifted (0,1cm)..(.5[check.nw,check.ne]) cutbefore bpath.unroll cutafter bpath.check;

  drawarrow .5[check.ne,check.se]..(.5[check.ne,check.se] shifted (4pt,-4pt))..diamok+(0,diamond_radius) cutbefore bpath.check;
  
  drawarrow diamok+(0,-diamond_radius)..(.5[checkct.ne,checkct.se] shifted (4pt,4pt))..(.5[checkct.ne,checkct.se]) cutafter bpath.checkct;

  drawarrow diamok+(diamond_radius,0)--diamok+(diamond_radius+2cm,0);
  label.top (btex [error found] etex, diamok+(diamond_radius+1cm,0));
  label.rt (btex report etex, diamok+(diamond_radius+2cm,0));

  pair diamnok;
  diamnok = (2cm,(ypart checkct.sw)-12pt);
  draw diamnok+(0,diamond_radius)--diamnok+(diamond_radius,0)--diamnok+(0,-diamond_radius)--diamnok+(-diamond_radius,0)--cycle;

  drawarrow (.5[checkct.se,checkct.sw])..(.5[checkct.se,checkct.sw] shifted (-4pt,-2pt))..diamnok+(diamond_radius,0) cutbefore bpath.checkct;

  drawarrow diamnok+(-diamond_radius,0)..(.5[increase.se,increase.sw] shifted (4pt,-2pt))..(.5[increase.se,increase.sw]) cutafter bpath.increase;

  drawarrow (.5[increase.nw,increase.sw])..(.5[unroll.sw,increase.nw]-(10pt,0))  ..(.5[unroll.nw,unroll.sw]);

  drawarrow diamnok+(0,-diamond_radius)--diamnok+(0,-diamond_radius-1cm);
  label.rt (btex [reached] etex, diamnok+(0,-diamond_radius-0.5cm));
  label.bot (btex OK etex, diamnok+(0,-diamond_radius-1cm));

  drawarrow unroll.nw+(-0.5cm,0.5cm)--unroll.nw cutafter bpath.unroll;
  label.top (btex C program etex, unroll.nw+(-0.5cm,0.5cm));
endfig;

end.
