for o in U O G; do for f in 0.25 0.5 0.75 1; do
 for mp in UU OO; do
  node multimode.js $mp $f $o nozero | py -c "
import sys,json;d=json.load(sys.stdin);t=d['top'][0];print('$o$f','map $mp','leaves',d['leaves'],'wins',d['wins'],'worst v %.4f'%t['v'],t['bits'])"
 done; done; done
