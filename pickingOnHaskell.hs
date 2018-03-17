mdule Track where
import Music

-- This is a simple program that plays a acoustic guitar chord picking that I wrote
--

main = writeMidi track "song"

-- cDelay is a helper function to delay a 'c' note by some specified amount
cDelay x = delay x (c 5 en [])

-- noteRepeat will repeat a note, or a group of notes by some specified amount n
noteRepeat n notes = line (take n (repeat notes))

-- the four definitions that follow make up a general finger picking pattern of a c chord ,am chord,
-- f chord and a g chord's notes. The c, am, and g chords each contain a call to the cDelay function which
-- enables a qn delay on the c note. This gives the impression of letting the "bass" note ring. 
 
cNotes  = line[ c 4 qn []] :=: cDelay qn :+: line[g 5 en[]] :+: 
               line[e 4 qn []] :=: cDelay qn :+: line[g 5 en[]]

amNotes = line[ a 4 qn []] :=: cDelay qn :+: line[ a 5 en[]] :+: 
               line[d 4 qn []] :=: cDelay qn :+: line[a 5 en[]]

fNotes    = line[ f 4 den[], cDelay sn, a 5 en[], 
                 f 4 den [], cDelay sn, a 5 en[]]

gBass     = line[ d 4 qn [], b 4 qn[], g 4 qn[]]
gRhythm   = line[ b 4 en [], g 4 en[]]
gPart     = chord[ gBass :=: gRhythm]

-- Below are 8 function definitions for chords c, am, f, g, d, d suspended
-- c over d (covD), d plus one(dPO). These chords were created so I could manipulate
--  their octave as well as their duration. 
cMaJ = [ n 4 en [] | n<-[c,e,g]]
aMin = [ n 4 qn [] | n<-[a,c,e]]
fMaj = [ n 4 qn [] | n<-[c,f,e]]
gMaj = [ n 4 en [] | n<-[g,b,d]]
dMaj = [ n 4 en [] | n<-[d,fs,a]]
dSus = [ n 4 en [] | n<-[d,e,a]]
covD = [ n 4 sn [] | n<-[e,g,d]] 
dPO  = [ n 4 en [] | n<-[d,g,a]]

-- picking describes how the notes of the c, am , f and g should be played. They are played in sequence and repeated,
--  using the noteRepeat function, twice.
picking = chord[ ( noteRepeat 2  cNotes :+: noteRepeat 2 amNotes) :+: (noteRepeat 2 fNotes) :+: (noteRepeat 2 gPart)]

-- tune augments the tempo of the pciking pattern to a 3/1 time and is also responsible for playing the picking pattern twice. 
-- following the picking, the time in set to 4/4 and four chords are played. 
tune = (Tempo(3%1) ((noteRepeat 2 picking))) :+: Tempo (4%4) (line[ chord cMaJ, (noteRepeat 2 (chord gMaj)), chord cMaJ])

-- chordie is an introduction set of chords played prior to the picking pattern. 
chordie = line [chord dMaj, chord cMaJ, chord dMaj, (noteRepeat 2 (chord dSus)),chord dMaj, chord covD, (noteRepeat 2 (chord dPO)), chord dMaj, chord gMaj, chord cMaj]

-- setting the instrument and playing the two parts of the song.
track = Instr "Acoustic Guitar" (chordie :+: tune) 

shorter :: Music -> Dur -> Bool
shorter m n 
          | dur' m > n = False
          | dur' m <= n = True

dur' :: Music -> Dur
dur' (Note _ d a) = d
dur' (Rest d) = d
dur' (m1 :+: m2) = dur' m1 + dur' m2
dur' (m1 :=: m2) = dur' m1 `max` dur' m2
dur' (Tempo a m) = dur' m / a
dur' (Trans _ m) = dur' m
dur' (Instr _ m) = dur' m



