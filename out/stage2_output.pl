expensive(0,0).
expensive(_58,_60):-_58>0,_60 is _58*_58.
p(_82,_84,_86):-expensive(_82,_92),_84 is _92+1,_86 is _92+2.
