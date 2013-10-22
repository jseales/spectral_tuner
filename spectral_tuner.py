#!/usr/bin/env python
# -*- coding: utf-8 -*-
import re
from random import random, choice, seed, shuffle
from copy import copy
from os.path import basename
import installFactoryFiles
import wx
import wx.lib.scrolledpanel as scrolledpanel
from math import cos, sin, pi, ceil, exp, log, floor
import graphTheory
import rtmidi
import time
import midi
import os


"""

An application to create tuning systems from sound timbres.

"""

##to do: Make a manual of the software
## document each individual function.
## Howto for some examples.

## for score, an overview of the music and correlation with drama
## overview of the total package, mentioning the different scope
## of the parts, perhaps mention intention to use generated music in synth parts.

#utility functions:

def Add(l1,l2):
    """Utility function that concatenates two lists. (Necessary for the reduce() fiunction.)"""
    return l1+l2

def And(b1,b2):
    """Utility function that finds the logical and of two boolean values.
    (Necessary for the reduce() function.)"""
    return b1 and b2

def ratioToSemitones(ratio):
    """Converts a frequency ratio into its semitone equivalent"""
    s = pow(2,1.0/12)
    semitones = log(ratio,s)
    return semitones

def semitonesToRatio(semitones):
    """Converts a semitone value into its frequency ratio equivalent"""
    ratio = pow(2,semitones/12.0)
    return ratio

def midinumToFrequency(midinum):
    """Converts a decimal midi number value into its frequency"""
    return 440*semitonesToRatio(midinum-69)

def frequencyToMidinum(frequency):
    """Converts a frequency into its decimal midi number equivalent"""
    return 69+ratioToSemitones(frequency/440.)

def weightedSelection(weightsAndChoices):
    """Makes a selection among the given choices randomly according to the given weight.
    for example, for weightsAndChoices=([1,'Dog'],[2,'Cat']) the function would be
    twice as likely to return 'Cat' as 'Dog'."""
    binEdges = [sum([wc[0] for wc in weightsAndChoices[:n]]) for n in range(len(weightsAndChoices)+1)]
    dieRoll=random()*binEdges[-1]
    
    for n in range(len(weightsAndChoices)):
        if binEdges[n+1]>dieRoll:
            return weightsAndChoices[n][1]


class spectrum(object):
    """The spectrum object contains a partialList and an amplitudeList.
    The lists must be of the same length. 'partialList' are floats;
    'amplitudeList' are integers."""
    
    def __init__(self,spectrumName,partialList,amplitudeList):
        """Sets up the spectrum object with its fields"""
           
        if len(partialList) != len(amplitudeList):
            wx.MessageBox('Partial- and amplitude-lists must be equal in length.',
                                   style=wx.CENTER|wx.ICON_ERROR|wx.OK)
         
        self.spectrumName = spectrumName
        self.partialList = partialList
        self.amplitudeList = amplitudeList


class gamut(dict):
    """A gamut is like a dictionary object, except that it returns False
        when inquired about a missing key instead of raising an Exception."""
    def __missing__(self,key):
        return False



class tuning(object):
    """The tuning object contains all of the note objects, along with several associated
    data fields, and a library of functions for manipulating and analyzing the tuning."""
    def __init__ (self):
        
        self.name = 'untitled tuning'

        self.coreNotes=gamut()
        self.coreCliques = []
        self.coreGraph=None
        self.coreConsonanceDict=gamut()
        self.coreIntervalDict=gamut()
        
        self.cycledNotes=gamut()
        self.cycledCliques = []
        self.cycledGraph=None
        self.cycledConsonanceDict=gamut()
        self.cycledIntervalDict=gamut()
        
        
        self.ConsonanceScore=0
        self.AlignedPartials=0
        
        self.intervalPossibilities=[[]]
        self.pConnectionDict=gamut()

        self.cycled = False
        

    def AddNote(self,midinum,initialPitch,anchorPitch,epsilon,spectrumName,partialList,amplitudeList):
        """Creates a note with the given values and adds it to the tuning."""
        self.coreNotes[midinum]=note(midinum,initialPitch,anchorPitch,epsilon,spectrumName,partialList,amplitudeList)
        
        
    def refreshConsonanceScore(self):
        """Called whenever a note's pitch is changed, or after groups of notes are added, this
        function keeps the recorded consonance score of the tuning current."""
        self.ConsonanceScore,self.AlignedPartials=self.measureConsonance(self.coreNotes.keys(),self.coreNotes)

    def makeConsonanceDict(self,noteGamut):
        """The ConsonanceDict's entries consist of keys: notes, and values:their
        consonance scores in relation to the rest of the tuning.
        If the consonance score is zero, no entry is made."""
        consonanceDict=gamut()
        pConnectionDict=gamut()
        midinums = sorted(noteGamut.keys())
        for m1 in midinums[:-1]:
            for m2 in midinums[midinums.index(m1)+1:]:
                c,p=self.measureConsonance([m1,m2],noteGamut)
                if c>0:
                    consonanceDict[(m1,m2)],pConnectionDict[(m1,m2)]=c,p
        return consonanceDict,pConnectionDict


    def makeIntervalPossibilities(self):
        """Find all the possible intervals between partial values
        of the spectra in the tuning. (Helper function for makeIntervalDict.)"""
        partialList=[]
        for n in self.coreNotes.keys():
            for p in self.coreNotes[n].spectrum.partialList:
                if p not in partialList:
                    partialList.append(p)
        self.intervalPossibilities=[[1,"1/\n1"]]
        for m in range(len(partialList)):
            for n in range(m):
                x = partialList[m]
                y = partialList[n]
                if type(x) == int:
                    xstring = str(x)
                if type(x) == float:
                    xstring = '{0:.2f}'.format(x)
                if type(y) == int:
                    ystring = str(y)
                if type(y) == float:
                    ystring = '{0:.2f}'.format(y)
                self.intervalPossibilities.append([float(x)/y,xstring+'/\n'+ystring])
                self.intervalPossibilities.append([float(y)/x,xstring+'/\n'+ystring])
        

    def makeIntervalDict(self,noteGamut):
        """A dictionary object between all pairs of midinums in the tuning and
        the interval between them if that interval is within one cent of a
        ratio interval between partial values of notes' spectra. If it is not,
        no entry is made."""
        midinums = sorted(noteGamut.keys())
        intervalDict = gamut()
        for i in midinums[:-1]:
            for j in midinums[midinums.index(i)+1:]:
                interval=float(noteGamut[j].freq)/noteGamut[i].freq
                for ip in self.intervalPossibilities:
                    if 0.999422 < interval/ip[0] < 1.000578:
                        intervalDict[(i,j)]=ip[1]
                        break
        return intervalDict


    def makeGraph(self,noteGamut,consonanceDict):
        """Makes the graph (nodes and edges) representation
        of the tuning. Makes it possible to find the cliques."""
        tuningGraph = graphTheory.graph()
        midinums = sorted(noteGamut.keys())
        for m in midinums:
            tuningGraph.add_node(m)
        for m1 in midinums[:-1]:
            for m2 in midinums[midinums.index(m1)+1:]:
                if consonanceDict[(m1,m2)]:
                    tuningGraph.add_edge(m1,m2)
        return tuningGraph
        

    def findCliques(self,graph,noteGamut,intervalDict):
        """finds the cliques in the tuning graph, and also determines
        whether they are otonalities, utonalites, or mixed."""
        result = []
        cliques=graph.find_all_cliques()
        
        for c in cliques:
            c = sorted(list(c))
            C = Clique(c)
            partials = reduce(Add,[noteGamut[n].spectrum.partialList for n in c])
            intervals = [['1','1']]+[intervalDict[(c[0],n)].split('/\n') for n in c[1:]]
            fractions = [[eval(i[0]),eval(i[1])] for i in intervals]
            numerators = [eval(i[0]) for i in intervals]
            denominators = [eval(i[1]) for i in intervals]
            maxnumerator=max(numerators)
            maxdenominator=max(denominators)
            newDenominators = [f[1]*float(maxnumerator)/f[0] for f in fractions]
            newNumerators = [f[0]*float(maxdenominator)/f[1] for f in fractions]
            utonality = reduce(And,[nD in partials for nD in newDenominators])
            otonality = reduce(And,[nN in partials for nN in newNumerators])
            if utonality:
                C.quality='utonality'
                C.denominators=newDenominators
            if otonality:
                C.quality='otonality'
                C.numerators=newNumerators
            result.append(C)

        return result


    def measureConsonance(self,midinums,noteGamut):
        """Measure the consonance by finding what partials coincide with each other,
            and score each coincidence of partials by the minimum of the amplitudes forming it."""
        ratioCent=1.00057778951
        fvec = reduce(Add,[noteGamut[m].partials for m in midinums])
        amp = reduce(Add,[noteGamut[m].spectrum.amplitudeList for m in midinums])
        M=len(fvec)
        f_amp = sorted([[fvec[m],amp[m]] for m in range(M)])
        fvec,amp=([f_amp[m][0] for m in range(M)],[f_amp[m][1] for m in range(M)])
        D=0
        P=0
        for i in range(1,M+1):
            for j in range(M-i):
                higher = fvec[i:][j]
                lower = fvec[:M-i][j]
                ratio = higher/lower
                if ratio < ratioCent:    
                    D+=min(amp[i:][j],amp[:M-i][j])
                    P+=1
        return D,P
                    
        


    def tuneOneNote(self,movingMidinum,fixedMidinums):
        """The note's range is divided into one-cent slots. The slots are shuffled
            and each retuning is tried. If the resulting shift in pitch
            increases the consonance score of the tuning as a whole, the note move is
            effected. If no move can increase the consonance score of the tuning, it is
            left in place."""
        af = self.coreNotes[movingMidinum].anchorFreq
        cents=int(100*self.coreNotes[movingMidinum].epsilon)
 
        ratioCent=1.00057778951

        #Setting other variables to get ready for tuning.
        referenceFreq=self.coreNotes[movingMidinum].freq
        minConsonance=self.ConsonanceScore
        result=-1
        order = range(-1*cents,cents)
        shuffle(order)
        n = 0
        
        #Move note around its range, and if it improves the tuning,
        #leave it there.
        while n < len(order):
            currFreq = pow(ratioCent,order[n])*af
            self.coreNotes[movingMidinum].move(currFreq)
            currConsonance,AP=self.measureConsonance([movingMidinum]+fixedMidinums,self.coreNotes)
            if currConsonance > minConsonance:
                self.ConsonanceScore = currConsonance
                self.AlignedPartials = AP
                e = self.coreNotes[movingMidinum].epsilon
                dlt = self.coreNotes[movingMidinum].pitch-self.coreNotes[movingMidinum].anchorPitch
                percentUp=int(100*(dlt+e)/(2*e))
                exec "app.TuningFrame.GaugePanel.Gauge"+str(movingMidinum)+".SetValue(percentUp)"
                exec "app.TuningFrame.GaugePanel.Gauge"+str(movingMidinum)+".Update()"
                app.TuningFrame.ConsonanceScoreTextCtrl.SetValue(str(minConsonance))
                app.TuningFrame.ConsonanceScoreTextCtrl.Update()
                app.TuningFrame.AlignedPartialsTextCtrl.SetValue(str(AP))
                app.TuningFrame.AlignedPartialsTextCtrl.Update()
                return True
            n+=1
            
        else:
            self.coreNotes[movingMidinum].move(referenceFreq)
            return False
        
    def tuneUp(self):
        """All notes are put in a random order. One at a time, a note's
            pitch is optimized against the rest of the notes in the tuning. When
            all notes have been tuned, the notes are reshuffled and each note is
            tuned again. The process iterates until the tuning passes through
            unaffected."""

        yellowgreen = wx.Colour(175,195,0,255)
        red = wx.Colour(205,18,0,255)
        green = wx.Colour(14,195,14,255)

        noteOrder = self.coreNotes.keys()
        if len(noteOrder)<2:
            wx.MessageBox("You must add at least two notes before you can tune them up.",
                          style=wx.CENTER|wx.ICON_ERROR|wx.OK)
            
        notLast=True
        while notLast:
            notLast = False
            shuffle(noteOrder)
            for i in range(len(noteOrder)):
                pd = "app.TuningFrame.GaugePanel.PitchDisplay"+str(noteOrder[i])
                if eval(pd+".GetForegroundColour()") == yellowgreen:
                    exec pd+".SetValue('tuning')"
                else:
                    exec pd+".SetValue('checking')"
                exec pd+".SetForegroundColour(red)"
                exec pd+".Update()"
                
                changed = self.tuneOneNote(noteOrder[i],noteOrder[:i]+noteOrder[i+1:])
                if changed:
                    exec pd+".SetForegroundColour(yellowgreen)"
                else:
                    exec pd+".SetForegroundColour(green)"
                            
                exec pd+".SetValue('{0:^.5}'.format(float(self.coreNotes[noteOrder[i]].pitch)))"
                exec pd+".Update()"
                notLast = notLast or changed
                
        ##Now that the tuning is done, construct some objects that will be used for analysis.
        self.coreConsonanceDict=self.makeConsonanceDict(self.coreNotes)[0]
        self.makeIntervalPossibilities()
        self.coreIntervalDict = self.makeIntervalDict(self.coreNotes)
        self.coreGraph=self.makeGraph(self.coreNotes,self.coreConsonanceDict)
        self.coreCliques=self.findCliques(self.coreGraph,self.coreNotes,self.coreIntervalDict)
        return True


    def cycle(self,lowestNote=30.0,highestNote=96.0):
        """Cycles a tuning throughout the effective range of the tuning. E.g., if a tuning spans an
        8/5 m6, the tuning will be duplicated every 8 midi numbers, and 8/5 frequency ratio,
        up and down throughout the given range."""

        nn = sorted(self.coreNotes.keys())

        #Set up the parameters of cycling the tuning.
        midinumCycleLength = nn[-1]-nn[0]
        pitchCycleLength=self.coreNotes[nn[-1]].pitch-self.coreNotes[nn[0]].pitch
        lowestCycle=int(-1*ceil(nn[0]-lowestNote/midinumCycleLength))
        highestCycle=int(ceil((highestNote-nn[0])/midinumCycleLength))

        #Cycle the tuning, store the notes and pitches in a dictionary.
        for o in range(lowestCycle,highestCycle):
            for n in nn[:-1]:
                N = self.coreNotes[n]
                newMidinum = midinumCycleLength*o+n
                newPitch = pitchCycleLength*o+N.pitch
                if lowestNote<=newMidinum<=highestNote:
                    self.cycledNotes[newMidinum]=note(newMidinum,newPitch,newPitch,N.epsilon,N.spectrum.spectrumName,N.spectrum.partialList,N.spectrum.amplitudeList)


        self.cycledConsonanceDict = self.makeConsonanceDict(self.cycledNotes)[0]
        self.cycledGraph = self.makeGraph(self.cycledNotes,self.cycledConsonanceDict)
        self.cycledIntervalDict=self.makeIntervalDict(self.cycledNotes)
        self.cycledCliques = self.findCliques(self.cycledGraph,self.cycledNotes,self.cycledIntervalDict)
        self.cycled = True
        
        

        
    def chooseByConsonance(self,tuneFrom,choices):
        """This function makes a weighted selection between the given choices
        based on their consonance value with the rest of the tuning.
        Choices can be individual notes or groups of notes."""
        weightsAndChoices=[]
        if type(tuneFrom[0])==list:
            tuneFrom=reduce(Add,tuneFrom)

        ###If c is a list, the 'try' block will be executed.
        ###If c is an integer, the 'except' block will be.
        try:
            for c in choices:
                weight=0
                for m1 in c:
                    for m2 in tuneFrom:
                        key = tuple(sorted([m1,m2]))
                        weight+=self.cycledConsonanceDict[key]
                weightsAndChoices.append([weight,c])
        except:
            for c in choices:
                weight=0
                for m2 in tuneFrom:
                    key = tuple(sorted([c,m2]))
                    weight+=self.cycledConsonanceDict[key]
                weightsAndChoices.append([weight,c])
        return weightedSelection(weightsAndChoices)


    def doNote(self,m,t,v,tSum,tempo):
        """This function sends a note to midi out."""
        midinumOn = rtmidi.MidiMessage.noteOn(0,m,v)
        midinumOff = rtmidi.MidiMessage.noteOff(0,m)
        self.midiout.sendMessage(midinumOn)
        
        nOn = midi.NoteOnEvent()
        nOn.pitch = m
        nOn.tick=480*tSum*tempo/60
        nOn.msdelay=1000*tSum
        
        time.sleep(t)
        
        self.midiout.sendMessage(midinumOff)

        nOff = midi.NoteOffEvent()
        nOff.pitch = m
        nOff.tick = 480*(tSum+(t*0.7))*tempo/60
        nOff.msdelay = 1000*(tSum+(t*0.7))

        return nOn,nOff

    def doChord(self,mList,t,v,tSum,tempo):
        """This function sends a Chord to midi out"""
        nOn = {}
        nOff = {}
        for m in mList:
            midinumOn = rtmidi.MidiMessage.noteOn(0,m,v)
            midinumOff = rtmidi.MidiMessage.noteOff(0,m)
            self.midiout.sendMessage(midinumOn)
            
            nOn[m] = midi.NoteOnEvent()
            nOn[m].pitch = m
            nOn[m].tick=480*tSum*tempo/60
            nOn[m].msdelay=1000*tSum
        
        time.sleep(t)
        
        self.midiout.sendMessage(midinumOff)

        for m in mList:
            nOff[m] = midi.NoteOffEvent()
            nOff[m].pitch = m
            nOff[m].tick = 480*(tSum+(t*0.7))*tempo/60
            nOff[m].msdelay = 1000*(tSum+(t*0.7))

        return nOn,nOff

    def saveMidi(self,stream):
        """Saves generated note sequences as a midi file."""
        wildcard = "SMidi Files (*.mid)|*.mid"
        dlg = wx.FileDialog(app.TuningFrame,message="Save Midi File As",
                            wildcard=wildcard,
                            style=wx.FD_SAVE|wx.FD_OVERWRITE_PROMPT,
                            defaultDir='/')
        if dlg.ShowModal() == wx.ID_OK:
            path=dlg.GetPath().strip('.mid')
            path+='.mid'

        midi.write_midifile(stream,path)

        dlg.Destroy()
            
               
    def generateMelody(self,order):
        """One of the musical generation functions; generates a melody using a nested
        Sierpinski Gasket form."""

        def sierpinskiGasket(elements,seed,order,clients=None):
            """On each iteration, new notes or groups of notes are added in each
            space between existing notes or groups of notes."""
            sequence=seed
            for i in range(order):
                indexes = range(1,len(sequence))
                indexes.reverse()
                for ix in indexes:
                    tunefrom=sequence[ix-1:ix+1]
                    choices = [e for e in elements if e not in tunefrom]
                    c = self.chooseByConsonance(tunefrom,choices)
                    sequence.insert(ix,c)
            if clients:
                sequence = [clients[elements.index(s)] for s in sequence]     
            return sequence


        def otonalChunk(clique,pulseLength,order=4,d=0.7,w=0.618):
            """If a clique is an otonality, rhythm is additive."""
            
            start = choice(clique.midinums)
            end = choice(clique.midinums)
            order = len(clique.midinums)


            neighbors = reduce(lambda x,y:x+y,[neighborTones(m) for m in clique.midinums])
            
            palette = list(set(neighbors+tuple(clique.midinums)))


            #makes a sequence of measure lengths by weighted choices.
            lengths = sierpinskiGasket(clique.midinums,[start,end],order,clients=clique.numerators)
            #picks a note for each measure that will be the first and last note in it.
            frameNotes = sierpinskiGasket(clique.midinums,[start,end],order,clients=None)
            
            highPoints = sierpinskiGasket(clique.midinums,[start,end],order,clients=[128*n/max(clique.numerators)-1 for n in clique.numerators])
            
            chunkNotes = []
            chunkVelocities = []
            
            for l,n,p in zip(lengths,frameNotes,highPoints):
                measure = {}
                velocities = {}
                l=int(l)
                measure[0]=n
                velocities[0]=int(d*p)
                measure[l-1]=n
                velocities[l-1]=int(d*p)
                for i in range(2,l):
                    measure[l-i]=self.chooseByConsonance([n,measure[l-i+1]],palette)
                    velocities[l-i]=int((p-d*p)/(w*(l-1))*(i-1)+d*p)
                chunkNotes+=[measure[i] for i in range(l)]
                chunkVelocities+=[velocities[i] for i in range(l)]

                
            chunkLengths = [pulseLength for n in chunkNotes]
        

            chunk = zip(chunkNotes,chunkLengths,chunkVelocities)
                
            return chunk


        def utonalChunk(clique,measureLength,order=4,d=0.7,w=0.618):
            """If the clique is an utonality, the rhythm is"""
            start=choice(clique.midinums)
            end=choice(clique.midinums)
            order = len(clique.midinums)

            neighbors = reduce(lambda x,y:x+y,[neighborTones(m) for m in clique.midinums])
            
            palette = list(set(neighbors+tuple(clique.midinums)))
            

            #makes a sequence of measure lengths by weighted choices.
            lengths = sierpinskiGasket(clique.midinums,[start,end],order,clients=clique.denominators)
            #picks a note for each measure that will be the first and last note in it.
            frameNotes = sierpinskiGasket(clique.midinums,[start,end],order,clients=None)

            highPoints = sierpinskiGasket(clique.midinums,[start,end],order,clients=[128*n/max(clique.numerators)-1 for n in clique.numerators])
            
            chunkNotes = []
            chunkLengths = []
            chunkVelocities = []
            
            for l,n,p in zip(lengths,frameNotes,highPoints):
                measure = {}
                velocities = {}
                l=int(l)
                measure[0]=n
                velocities[0]=int(0.7*p)
                measure[l-1]=n
                velocities[l-1]=int(p)
                for i in range(2,l):
                    measure[l-i]=self.chooseByConsonance([n,measure[l-i+1]],palette)
                    velocities[l-i]=int((p-d*p)/(w*(l-1))*(i-1)+d*p)
                chunkNotes+=[measure[i] for i in range(l)]
                chunkLengths+=[float(measureLength)/l for i in range(l)]
                chunkVelocities+=[velocities[i] for i in range(l)]

                

            chunk = zip(chunkNotes,chunkLengths,chunkVelocities)
                
            return chunk
              

        def neighborTones(midinum):
            """Finds upper and lower neighbors to a given note."""
            upperNeighbor=None
            lowerNeighbor=None
            if self.cycledNotes[midinum]:
                upperNeighbor=midinum+1
                while not self.cycledNotes[upperNeighbor]:
                    upperNeighbor+=1
                    if upperNeighbor>127:
                        upperNeighbor=None
                        break
                lowerNeighbor=midinum-1
                while not self.cycledNotes[lowerNeighbor]:
                    lowerNeighbor-=1
                    if lowerNeighbor<0:
                        lowerNeigbor=None
                        break

            return lowerNeighbor,upperNeighbor



        if not self.cycled:
            self.cycle()
        
        startClique = choice(self.cycledCliques)
        startMidinums=startClique.midinums
        cliqueMidinums=[c.midinums for c in self.cycledCliques]
        cliqueList=sierpinskiGasket(cliqueMidinums,[startMidinums,startMidinums],order,clients=self.cycledCliques)
            


        midinumsTimesVelocities=[]
        for clique in cliqueList:                
            if clique.quality == 'otonality':
                chunk = otonalChunk(clique,0.25)
                midinumsTimesVelocities+=chunk

            elif clique.quality == 'utonality':
                chunk = utonalChunk(clique,1)
                midinumsTimesVelocities+=chunk

        self.midiout=rtmidi.RtMidiOut()
        self.midiout.openPort(0)
                
        tempo = 120

        tSum = 0
        X = midi.EventStream()
        X.resolution=480
        X.add_track()

        tempoEvent = midi.SetTempoEvent()
        tempoEvent.tempo = tempo
        X.add_event(tempoEvent)
        
        for m,t,v in midinumsTimesVelocities:
            nOn,nOff=self.doNote(m,t,v,tSum,tempo)
            X.add_event(nOn)
            X.add_event(nOff)
            tSum+=t

        self.saveMidi(X)
    
    def generateChords(self,l,t=1):
        """Generates a sequence of chords by wieghted selections based on consonance."""
      
        if not self.cycled:
            self.cycle()

        chordSequence={}
            
        chordSequence[l-1] = sorted(choice(self.cycledCliques).midinums)
        chordSize = len(chordSequence[l-1])

        for i in range(l-2,-1,-1):
            chordSequence[i]=range(chordSize)
            for j in range(chordSize):
                if j==0:
                    bounds=0,chordSequence[i+1][1]
                elif j==chordSize-1:
                    bounds=chordSequence[i+1][j-1],127
                else:
                    bounds=chordSequence[i+1][j-1],chordSequence[i+1][j+1]
                print 'bounds',bounds
                palette = [m for m in range(*bounds) if m in self.cycledNotes]
                tuneFrom = chordSequence[i+1]+[chordSequence[i+1][j]]
                if not palette:
                    chordSequence[i][j]=chordSequence[i][j-1]
                else:
                    chordSequence[i][j]=self.chooseByConsonance(tuneFrom,palette)
            chordSequence[i]=sorted(chordSequence[i])
        
        tempo = 120

        tSum = 0
        X = midi.EventStream()
        X.resolution=480
        X.add_track()

        tempoEvent = midi.SetTempoEvent()
        tempoEvent.tempo = tempo
        X.add_event(tempoEvent)
        
        self.midiout=rtmidi.RtMidiOut()
        self.midiout.openPort(0)
               
        nOn,nOff=self.doChord(chordSequence[i],t,90,tSum,tempo)
        for m in chordSequence[i]:
            X.add_event(nOn[m])
            X.add_event(nOff[m])
        tSum+=t

        self.saveMidi(X)
            

    def generateFirstOrder(self,n):
        """Generates a note sequence by a first-order markov chain. Rhythmic values
        have the same relationship as frequency values."""
        if not self.cycled:
            self.cycle()
        
        startClique = choice(self.cycledCliques)
        cliqueMidinums = startClique.midinums

        pulse = 0.5
        curr = choice(cliqueMidinums)

        midiout=rtmidi.RtMidiOut()
        midiout.openPort(0)
        
        for i in range(n*2):
            subsequent = self.chooseByConsonance([curr],self.cycledNotes.keys())
                
            midinumOn = rtmidi.MidiMessage.noteOn(0,curr,90)
            midiout.sendMessage(midinumOn)
            
            time.sleep(pulse)
            
            midinumOff = rtmidi.MidiMessage.noteOff(0,curr)
            midiout.sendMessage(midinumOff)

            
            ratio = self.cycledNotes[subsequent].pitch/self.cycledNotes[curr].pitch
            pulse /= ratio
            curr = subsequent

            
    def generateBombs(self,n):
        """Generates descending melodic lines based on weighted selections by consonance."""
        if not self.cycled:
            self.cycle()
        
        coreNotes=sorted(self.coreNotes.keys())
        rootNote=coreNotes[0]
        cycleSize=coreNotes[-1]-rootNote

        cycledNotes=sorted(self.cycledNotes.keys())
        bottomNote=cycledNotes[0]
        topNote=cycledNotes[-1]

        cyclesAboveCore = (topNote-rootNote)/cycleSize-1
        cyclesBelowCore = (bottomNote-rootNote)/cycleSize

        midiout=rtmidi.RtMidiOut()
        midiout.openPort(0)

        
        
        for clique in self.coreCliques:
            cliqueMidinums=sorted(clique.midinums,reverse=True)
            prev = False
            pulse = 1.2
            for i in range(cyclesAboveCore,cyclesBelowCore,-1):
                for m in cliqueMidinums:
                    curr=m+i*cycleSize
                    
                    midinumOn=rtmidi.MidiMessage.noteOn(0,curr,90)
                    midiout.sendMessage(midinumOn)
                    
                    time.sleep(pulse)
                    
                    midinumOff = rtmidi.MidiMessage.noteOff(0,curr)
                    midiout.sendMessage(midinumOff)

                    if prev:
                        pulse *= self.cycledNotes[curr].freq/self.cycledNotes[prev].freq
                    prev=curr
            cliqueMidinums.reverse()
            for i in range(cyclesBelowCore+1,cyclesAboveCore+1):
                for m in cliqueMidinums:
                    curr=m+i*cycleSize
                    
                    midinumOn=rtmidi.MidiMessage.noteOn(0,curr,90)
                    midiout.sendMessage(midinumOn)
                    
                    time.sleep(pulse)
                    
                    midinumOff = rtmidi.MidiMessage.noteOff(0,curr)
                    midiout.sendMessage(midinumOff)

                    print 'prev,curr',prev,curr
                    if prev:
                        pulse *= self.cycledNotes[curr].freq/self.cycledNotes[prev].freq
                    prev=curr


                    

            
        
        
class note(object):
    """The note object stores its midi number, its exact pitch and frequency
    (pitch is recorded in midi numbers, frequency in Hz), its anchor pitch and epsilon
    (a note can be retuned a maximum <epsilon> distance from the anchor pitch)
    its spectrum and partials (spectrum is the partial ratios to the fundamental;
    partials are the frequency values for the note at its current tuning.)"""
    def __init__(self,midinum,initialPitch,anchorPitch,epsilon,spectrumName,partialList,amplitudeList):
        self.midinum=midinum
        self.pitch = initialPitch
        self.anchorPitch=anchorPitch
        self.epsilon=epsilon
        self.spectrum=spectrum(spectrumName,partialList,amplitudeList)

        self.freq = midinumToFrequency(self.pitch)
        self.anchorFreq=midinumToFrequency(self.anchorPitch)
        self.epsilonRatio=semitonesToRatio(self.epsilon)
        self.partials=[self.freq * p for p in self.spectrum.partialList]


    def move(self,f):
        """Refreshes the appropriate values in the note object
        when the note is retuned."""
        self.freq=f
        self.pitch=frequencyToMidinum(f)
        self.partials=[f*p for p in self.spectrum.partialList]

class Clique(object):
    """A clique is a set of note objects that are all related to each other by frequency
    ratios that are equal to ratios between partial values in the notes' spectra."""
    def __init__(self,midinums):
        self.midinums = sorted(midinums)
        self.quality = ''
        self.numerators = []
        self.denominators = []








##The View... The rest of the functions relate to the GUI, and the user's control of the program.
      


##widgets in "Tuning" frame
LOAD_TUNING_BUTTON_ID = wx.NewId()
CLEAR_TUNING_BUTTON_ID = wx.NewId()
GAUGE_LINE_ID=wx.NewId()
ADD_BUTTON_ID = wx.NewId()
TUNE_UP_BUTTON_ID = wx.NewId()
EXPORT_DOT_TUN_ID = wx.NewId()
SAVE_TUNING_BUTTON_ID = wx.NewId()
INTERVAL_TABLE_ID = wx.NewId()
CLIQUES_BUTTON_ID = wx.NewId()
GENERATE_MELODY_BUTTON_ID = wx.NewId()
GENERATE_CHORDS_BUTTON_ID = wx.NewId()
GENERATE_FIRST_ORDER_BUTTON_ID = wx.NewId()
GENERATE_BOMBS_BUTTON_ID = wx.NewId()

##widgets in "Add Notes" frame
INTERVAL_PATTERN_TEXTCTRL_ID = wx.NewId()
ROOT_NOTE_TEXTCTRL_ID = wx.NewId()
INITIAL_PITCHES_CB_ID = wx.NewId()
ANCHOR_PITCHES_CB_ID = wx.NewId()
EPSILON_TEXTCTRL_ID = wx.NewId()
CREATE_SPECTRUM_BUTTON_ID = wx.NewId()
LOAD_SPECTRUM_ID = wx.NewId()
SPECTRUM_COMBOBOX_ID = wx.NewId()
DONE_BUTTON_ID = wx.NewId()
CANCEL_ADDNOTES_BUTTON_ID = wx.NewId()

##widgets in "Create Spectrum" frame
PARTIAL_VALUES_TEXTCTRL_ID = wx.NewId()
PARTIAL_INTENSITIES_TEXTCTRL_ID = wx.NewId()
SAVE_SPECTRUM_BUTTON_ID = wx.NewId()
SAVE_SPECTRUM_AS_BUTTON_ID = wx.NewId()

##widget in "Initial Pitches" frame
INITIAL_PITCHES_TEXTCTRL_ID = wx.NewId()

##widget in "Anchor Pitches" frame
ANCHOR_PITCHES_TEXTCTRL_ID = wx.NewId()

##widgets in "Cliques" frame
SHOW_INTERVAL_TABLE_ID = wx.NewId()
SHOW_EDGE_LABELS_ID = wx.NewId()
LISTEN_ID = wx.NewId()




class ConfigHelper(object):
    """This is a helper class to detect and/or create folders on the user's
        computer to store facory and user spectra and tunings. """
    def __init__(self, userdirs=None):
        """@keyword userdirs: list of user config subdirectories names"""
        super(ConfigHelper, self).__init__()
        # Attributes self.userdirs = userdirs
        # Setup self.InitializeConfig()

    def InitializeConfig(self):
        """Setup config directories"""
        # Create main user config directory if it does
        # not exist.
        datap = wx.StandardPaths_Get().GetUserDataDir()
        if not os.path.exists(datap):
            os.mkdir(datap)
            # Make sure that any other application specific
            # config subdirectories have been created.
        if self.userdirs:
            for dname in userdirs:
                self.CreateUserCfgDir(dname)
                
    def CreateUserCfgDir(self, dirname):
        """Create a user config subdirectory"""
        path = wx.StandardPaths_Get().GetUserDataDir()
        path = os.path.join(path, dirname)
        if not os.path.exists(path):
            os.makedirs(path)

    def GetUserConfigPath(self, relpath):
        """Get the path to a resource file in the users
        configuration directory.@param relpath: relative
        path (i.e config.cfg) @return: string """
        path = wx.StandardPaths_Get().GetUserDataDir()
        path = os.path.join(path, relpath)
        return path

    def HasConfigFile(self, relpath):
        """Does a given config file exist"""
        path = self.GetUserConfigPath(relpath)
        return os.path.exists(path)



class PersistentFrame(wx.Frame):
    """This is a frame that saves information about its state, size,
       and location upon closing. The other frames inherit from this class"""
    def __init__(self, *args, **kwargs):
        super(PersistentFrame, self).__init__(*args, **kwargs)
        # Setup
        wx.CallAfter(self.RestoreState)

        # Event Handlers
        self.Bind(wx.EVT_CLOSE, self._OnClose)

        #Here, we handle EVT_CLOSE for when the Frame is closing,
        #in order to save its position and size to the Config object,
        #which is the registry on Windows and a .ini file on other platforms:
    def _OnClose(self, event):
        position = self.GetPosition()
        size = self.GetSize()
        cfg = wx.Config()
        cfg.Write('pos', repr(position.Get()))
        cfg.Write('size', repr(size.Get()))
        event.Skip()

        #The RestoreState method restores the currently-stored window
        #state or the default state if nothing has been stored yet:
    def RestoreState(self):
        """Restore the saved position and size"""
        cfg = wx.Config()
        name = self.GetName()
        position = cfg.Read(name + '.pos',
                            repr(wx.DefaultPosition))
        size = cfg.Read(name + '.size',
                        repr(wx.DefaultSize))
        # Turn strings back into tuples
        position = eval(position)
        size = eval(size)
        # Restore settings to Frame
        self.SetPosition(position)
        self.SetSize(size)


class IntervalTableFrame(wx.Frame):
    """Creates a table showing an where there exist
        intervals that are ratios between partial values."""
    
    def __init__(self, parent, id=wx.ID_ANY,
                 title="Interval Table",
                 pos=(800,30), size = (377,154),
                 style=wx.DEFAULT_FRAME_STYLE,
                 name="IntervalTableFrame"):
        super(IntervalTableFrame, self).__init__(parent,id,title,pos,size,style,name)

        self.intervalTableNotes = []

    def setupTable(self):
        
        self.N = len(self.intervalTableNotes)
        self.SetSize(((self.N+1)*50,(self.N+1)*50))
        self.sizer=wx.GridSizer(rows=self.N+1,cols=self.N+1,hgap=5,vgap=5)

        intervalDict = app.TuningFrame.tuning.coreIntervalDict
        
        for i in range(-1,self.N):
            for j in range(-1,self.N):
                value = ''
                if i == -1 and j == -1:
                    style=wx.NO_BORDER
                elif i == -1:
                    value=str(self.intervalTableNotes[j])
                    style=wx.NO_BORDER                                         
                elif j == -1:
                    value=str(self.intervalTableNotes[i])
                    style=wx.NO_BORDER
                elif i<j:
                    if intervalDict[(self.intervalTableNotes[i],self.intervalTableNotes[j])]:
                        value=intervalDict[(self.intervalTableNotes[i],self.intervalTableNotes[j])]
                        style=wx.SIMPLE_BORDER
                    else:
                        value = '-'
                        style=wx.NO_BORDER

                self.sizer.Add(wx.StaticText(self,-1,value,style=style))
                
        self.SetSizer(self.sizer)


class CliqueFrame(wx.Frame):
    """Represents the tuning as a graph whose nodes are the notes,
        and whose edges are the ratio intervals as found in the
        'interval table.' (see above.)"""
    def __init__(self, parent, id=wx.ID_ANY,
                 title="Clique",
                 pos=(0,30), size = (700,700),
                 style=wx.DEFAULT_FRAME_STYLE,
                 name="CliqueFrame"):
        super(CliqueFrame, self).__init__(parent,id,title,pos,size,style,name)

        ##Class Attributes
        self.L,self.W=self.GetSize()
        self.Bind(wx.EVT_PAINT, self.drawGraphs)
        self.EdgeLabelList = []
        self.nodeWeights={}
        self.edgeLabelsShown=False
        ##The client function will set self.cliqueNotes to the notes in the clique.
        self.cliqueNotes=None

        
        vsizer=wx.BoxSizer(wx.VERTICAL)
        vsizer.AddSpacer(50) 
        
        hsizer=wx.BoxSizer(wx.HORIZONTAL)
        hsizer.AddSpacer(20) 
        self.ShowIntervalTableButton=wx.Button(self,
                                          label="Interval Table",
                                          id=SHOW_INTERVAL_TABLE_ID)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickShowIntervalTable,
                  self.ShowIntervalTableButton)
        hsizer.Add(self.ShowIntervalTableButton)
        hsizer.AddSpacer(430)
        
        self.ShowEdgeLabelsButton=wx.Button(self,
                                      label="Edge Labels",
                                      id=SHOW_EDGE_LABELS_ID)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickShowEdgeLabels,
                  self.ShowEdgeLabelsButton)
        hsizer.Add(self.ShowEdgeLabelsButton)
        vsizer.Add(hsizer)

        vsizer.AddSpacer(80)

        hsizer2=wx.BoxSizer(wx.HORIZONTAL)
        hsizer2.AddSpacer(20)

        self.ListenButton=wx.Button(self,
                                      label="Listen",
                                      id=LISTEN_ID)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickListen,
                  self.ListenButton)
        hsizer2.Add(self.ListenButton)
        
        vsizer.Add(hsizer2)
        
        self.SetSizer(vsizer)
               
        
    def drawGraphs(self,event):
        """Draws a node for each note, and an edge for each interval that is
        a ratio between partial values of the notes' spectra"""

        ##Setting up the drawing.
        nn = sorted(app.TuningFrame.tuning.coreNotes.keys())
        N = len(nn)
        
        ##Drawing the clique.
        self.dc = wx.PaintDC(event.GetEventObject())
        self.dc.Clear()
        self.dc.SetPen(wx.Pen("BLACK",3.7))

        centerX=self.W/2
        centerY=self.W/2
        r1 = 9*self.W/20
        r2 = 3*self.W/8


        self.dc.DrawCircle(centerX,centerY, r1)
    
        cD=app.TuningFrame.tuning.coreConsonanceDict
        avgConsonance=sum(cD.values())/len(cD.values())
        maxConsonance=max(cD.values())
        minConsonance=min(cD.values())
        for n in self.cliqueNotes[:-1]:
            for m in self.cliqueNotes[self.cliqueNotes.index(n)+1:]:                
                if cD[(n,m)]:
                    value = 1+7*(cD[(n,m)]-minConsonance)/(maxConsonance-minConsonance)
                    if value < 1.33:
                        color="VIOLET"
                    elif value < 2.66:
                        color="BLUE"
                    elif value < 4:
                        color="GREEN"
                    elif value < 5.33:
                        color="YELLOW"
                    elif value < 6.66:
                        color="GOLD"
                    else:
                        color="RED"                 
                    self.dc.SetPen(wx.Pen(color,value))
                    intervalText = str(app.TuningFrame.tuning.coreIntervalDict[(n,m)])

                    Wn=(nn.index(n)*2*pi/N)-pi/2
                    Wm=(nn.index(m)*2*pi/N)-pi/2
                    x1=int(centerX+cos(Wn)*r2)
                    y1=int(centerX+sin(Wn)*r2)
                    x2=int(centerY+cos(Wm)*r2)
                    y2=int(centerY+sin(Wm)*r2)
                    
                    self.dc.DrawLine(x1,y1,x2,y2)
                    midpointx,midpointy = (x2+x1)/2,(y2+y1)/2
                    if abs(midpointx-centerX)<2 and abs(midpointy-centerY)<2:
                        midpointx+=int(cos(Wn)*50)
                        midpointy+=int(sin(Wn)*50)
                       
                    self.EdgeLabelList.append((intervalText,midpointx,midpointy))
                                                  
        for k in self.cliqueNotes:
            self.nodeWeights[k]=0
            for edge in cD.keys():
                if k in edge:
                    self.nodeWeights[k]+=cD[edge]

        avgWeight=sum(self.nodeWeights.values())/len(self.cliqueNotes)
        
                     
        for k in self.cliqueNotes:
            Wk=(nn.index(k)*2*pi/N)-pi/2
            x=int(centerX+cos(Wk)*r2)
            y=int(centerY+sin(Wk)*r2)
            self.dc.SetPen(wx.Pen("GREEN",1))
            circleSize = 20*self.nodeWeights[k]/avgWeight
            self.dc.DrawCircle(x,y,circleSize)
            self.dc.DrawText(str(k),x-8,y-8)

    def OnClickShowIntervalTable(self,event):
        """Allows the user to request an interval table within the clique frame."""
        self.IntervalTableFrame = IntervalTableFrame(self)
        self.IntervalTableFrame.intervalTableNotes = self.cliqueNotes
        self.IntervalTableFrame.SetTitle(self.GetTitle()+' intervals')
        self.IntervalTableFrame.setupTable()
        self.IntervalTableFrame.Show()

    def OnClickShowEdgeLabels(self,event):
        """Labels each edge in the graph with its ratio."""
        if not self.edgeLabelsShown:
            for el in self.EdgeLabelList:
                self.dc.DrawText(*el)
        else:
            self.dc.Clear()
        
        self.edgeLabelsShown = not self.edgeLabelsShown

    def OnClickListen(self,event):
        """Plays each note in the clique in ascending order, then
        all of them as a chord."""
        midiout=rtmidi.RtMidiOut()
        midiout.openPort(0)
        for k in self.cliqueNotes:
            midinumOn = rtmidi.MidiMessage.noteOn(0,k,90)
            midiout.sendMessage(midinumOn)

            time.sleep(1)

            midinumOff = rtmidi.MidiMessage.noteOff(0,k)
            midiout.sendMessage(midinumOff)

        time.sleep(1)
        
        for k in self.cliqueNotes:
            midinumOn = rtmidi.MidiMessage.noteOn(0,k,90)
            midiout.sendMessage(midinumOn)

        time.sleep(2)

        for k in self.cliqueNotes:
            midinumOff = rtmidi.MidiMessage.noteOff(0,k)
            midiout.sendMessage(midinumOff)
        


class CreateSpectrumFrame(wx.Frame):
    """This is the frame for the user to create custom spectra."""
    def __init__(self, parent, id=wx.ID_ANY, title="Untitled Spectrum",
                 pos=(800,30), size = (377,154),
                 style=wx.DEFAULT_FRAME_STYLE,
                 name="CreateSpectrumFrame"):
        super(CreateSpectrumFrame, self).__init__(parent,id,title,pos,size,style,name)

        
        #Attributes
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.AddSpacer(10)

        ##The line for the 'partial values' text control
        PVSizer=wx.BoxSizer(wx.HORIZONTAL)
        PVSizer.AddSpacer(30)
        PVSizer.Add(wx.StaticText(self, label="List values of partials"))
        PVSizer.AddSpacer(31)
        self.PartialListCtrl=wx.TextCtrl(self,size=(170,20),
                                         id=PARTIAL_VALUES_TEXTCTRL_ID)
        self.PartialListCtrl.SetToolTipString("format: decimals separated by spaces")
        PVSizer.Add(self.PartialListCtrl)
        sizer.Add(PVSizer)

        sizer.AddSpacer(10)

        ##The line for the 'partial intensities' text control
        PISizer=wx.BoxSizer(wx.HORIZONTAL)
        PISizer.AddSpacer(30)
        PISizer.Add(wx.StaticText(self, label="List intensities of partials"))
        PISizer.AddSpacer(5)
        self.AmplitudeListCtrl=wx.TextCtrl(self,size=(170,20),
                                           id=PARTIAL_INTENSITIES_TEXTCTRL_ID)
        self.AmplitudeListCtrl.SetToolTipString("format: integers separated by spaces")
        PISizer.Add(self.AmplitudeListCtrl)
        sizer.Add(PISizer)

        sizer.AddSpacer(10)

        ##This line defines the 'save spectrum' and 'save spectrum as' button
        SSSizer=wx.BoxSizer(wx.HORIZONTAL)
        SSSizer.AddSpacer(30)
        self.SaveSpectrumButton=wx.Button(self,
                                          label="Save Spectrum",
                                          id=SAVE_SPECTRUM_BUTTON_ID)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickSaveSpectrum,
                  self.SaveSpectrumButton)
        SSSizer.Add(self.SaveSpectrumButton)
        
        sizer.Add(SSSizer)

        self.SetSizer(sizer)
                    
    ##Methods
    def OnClickSaveSpectrum(self, event):
        """Checks if the user-provided values make sense, and if so,
        saves the spectrum in a file."""
        
        OKtoSave = True

        ##Catch bad values for the partial list and ask the user to fix them.
        partialListString=self.PartialListCtrl.GetValue()
        partialList=partialListString.split()
        try:
            partialList=[float(n) for n in partialList]
        except:
            wx.MessageBox("Partial list must be numbers separated by spaces.",
                                   style=wx.CENTER|wx.ICON_ERROR|wx.OK)
            OKtoSave = False

        ##Catch bad values for the amplitude list and ask the user to fix them.                        
        amplitudeListString=self.AmplitudeListCtrl.GetValue()
        amplitudeList=amplitudeListString.split()
        try:
            amplitudeList=[float(n) for n in amplitudeList]
        except:
            wx.MessageBox("Amplitude list must be numbers separated by spaces.",
                                   style=wx.CENTER|wx.ICON_ERROR|wx.OK)
            OKtoSave = False

        #Check that the lists are not empty.    
        if len(partialList)<1 or len(amplitudeList)<1:
            wx.MessageBox("Neither list can be empty.",
                                   style=wx.CENTER|wx.ICON_ERROR|wx.OK)
            OKtoSave = False

        #Check that the two lists have equal length. 
        if len(partialList)!=len(amplitudeList):
            wx.MessageBox("List lengths must be equal",
                                   style=wx.CENTER|wx.ICON_ERROR|wx.OK)
            OKtoSave = False    

        #If the lists pass muster, go ahead with the saving. 
        if OKtoSave:
            evt_id = event.GetId()
            if evt_id == wx.ID_SAVE:
                self.DoSaveSpectrumAs()
            else:
                self.DoSaveSpectrumAs()


    def DoSaveSpectrumAs(self):
        """Carries out the saving of the spectrum file"""
        wildcard = "Spectrum Files (*.spc)|*.spc"
        dlg = wx.FileDialog(self,message="Save Spectrum As",
                            wildcard=wildcard,
                            style=wx.FD_SAVE|wx.FD_OVERWRITE_PROMPT,
                            defaultDir=app.config.GetUserConfigPath("Spectra/User Spectra"))
        if dlg.ShowModal() == wx.ID_OK:
            path=dlg.GetPath().strip('.spc')
            self.DoSaveSpectrum(path+'.spc')
            self.SetTitle(basename(path))
            app.TuningFrame.AddNotesFrame.SpectrumComboBox.Append(basename(path))
            app.TuningFrame.AddNotesFrame.SpectrumComboBox.SetValue(basename(path))
            self.Hide()
        dlg.Destroy()


    def DoSaveSpectrum(self,path):
        """Constructs the text to write in the spectrum file."""
        partialList = self.PartialListCtrl.GetValue().split()
        amplitudeList = self.AmplitudeListCtrl.GetValue().split()
        with open(path,"wb") as handle:
            text ="spectrumName='"+basename(path).strip('.spc')+"'\n"+\
                   "partialList=["+','.join([str(x) for x in partialList])+"]\n"+\
                   "amplitudeList=["+','.join([str(x) for x in amplitudeList])+"]\n"
            handle.write(text)
        
                       

class AddNotesFrame(PersistentFrame):
    """This is the frame to create notes for use in the tuning."""
    def __init__(self, parent, id=wx.ID_ANY, title="Add Notes",
                 pos=(600,30), size = (352,444),
                 style=wx.DEFAULT_FRAME_STYLE,
                 name="AddNotesFrame"):
        super(AddNotesFrame, self).__init__(parent,id,title,pos,size,style,name)

        self.RestoreState()
    
        #Attributes
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.AddSpacer(10)
        
        
        ##the text control where you specify the notes to Add
        ##by inputting an interval pattern and a starting note.
        TCSizer=wx.BoxSizer(wx.HORIZONTAL)
        TCSizer.AddSpacer(30)
        TCSizer.Add(wx.StaticText(self, label="Interval Pattern:"))
        TCSizer.AddSpacer(5)
        self.IntervalPatternTextCtrl=wx.TextCtrl(self,
                                            id = INTERVAL_PATTERN_TEXTCTRL_ID)
        self.Bind(wx.EVT_TEXT,
                  self.OnIntervalPatternUpdate,
                  self.IntervalPatternTextCtrl)
        self.IntervalPatternTextCtrl.SetToolTipString("in semitones. E.g. 2 2 1 2 2 2 1 for the major "+\
                                                    "scale, 2 1 2 2 for a pattern repeating at the P5.")
        self.IntervalPatternTextCtrl.SetValue('2 2 1 2 2 2 1')
        TCSizer.Add(self.IntervalPatternTextCtrl)
        TCSizer.AddSpacer(10)
        TCSizer.Add(wx.StaticText(self, label="Root Note:"))
        TCSizer.AddSpacer(5)
        self.RootNoteTextCtrl=wx.TextCtrl(self,
                                              id=ROOT_NOTE_TEXTCTRL_ID,
                                              size=(25,20))
        self.Bind(wx.EVT_TEXT,
                  self.OnRootNoteUpdate,
                  self.RootNoteTextCtrl)
        self.RootNoteTextCtrl.SetToolTipString("A midi number that begins the interval "+\
                                             "pattern.For example, input 60 -middle C- "+\
                                             "(with a major scale interval pattern) "+\
                                               "for a C major scale throughout the gamut.")
        self.RootNoteTextCtrl.SetValue('60')
        TCSizer.Add(self.RootNoteTextCtrl)
        sizer.Add(TCSizer)

        sizer.AddSpacer(20)

        ##The line where you uncheck a box if you want to define initial pitches.
        IPSizer=wx.BoxSizer(wx.HORIZONTAL)
        IPSizer.AddSpacer(30)
        self.InitialPitchesCB=wx.CheckBox(self,id=INITIAL_PITCHES_CB_ID)
        self.InitialPitchesCB.SetValue(True)
        self.Bind(wx.EVT_CHECKBOX,
                  self.OnIPBoxChange,
                  self.InitialPitchesCB)
        IPSizer.Add(self.InitialPitchesCB)
        IPSizer.AddSpacer(5)
        IPSizer.Add(wx.StaticText(self,
                                  label="Use midi numbers as initial pitches?"))
        sizer.Add(IPSizer)
        
        sizer.AddSpacer(2)

        ##On this line you define the initial pitches if you want.
        IPTextSizer = wx.BoxSizer(wx.HORIZONTAL)
        IPTextSizer.AddSpacer(30)
        IPTextSizer.Add(wx.StaticText(self,label="List initial pitches:"))
        IPTextSizer.AddSpacer(5)
        self.InitialPitchesTextCtrl=wx.TextCtrl(self,size=(150,20),
                                                id=INITIAL_PITCHES_TEXTCTRL_ID)
        self.Bind(wx.EVT_TEXT,
                  self.OnIPTextChange,
                  self.InitialPitchesTextCtrl)
        self.InitialPitchesTextCtrl.SetToolTipString("Input a list of decimals as the "+\
                                                     "initial pitches. It must be one "+\
                                                     "longer than the interval pattern.")
        IPTextSizer.Add(self.InitialPitchesTextCtrl)
        sizer.Add(IPTextSizer)
        sizer.AddSpacer(10)

        ##The line where you uncheck a box to say if you want to define anchor pitches.
        APSizer=wx.BoxSizer(wx.HORIZONTAL)
        APSizer.AddSpacer(30)
        self.AnchorPitchesCB=wx.CheckBox(self,id=ANCHOR_PITCHES_CB_ID)
        self.AnchorPitchesCB.SetValue(True)
        self.Bind(wx.EVT_CHECKBOX,
                  self.OnAPBoxChange,
                  self.AnchorPitchesCB)
        APSizer.Add(self.AnchorPitchesCB)
        APSizer.AddSpacer(5)
        APSizer.Add(wx.StaticText(self, label="Use midi numbers as anchor pitches?"))
        sizer.Add(APSizer)

        sizer.AddSpacer(2)

        ##Here you define the anchor pitches if you want.
        APTextSizer = wx.BoxSizer(wx.HORIZONTAL)
        APTextSizer.AddSpacer(30)
        APTextSizer.Add(wx.StaticText(self,label="List Anchor pitches:"))
        APTextSizer.AddSpacer(5)
        self.AnchorPitchesTextCtrl=wx.TextCtrl(self,size=(150,20),
                                                id=ANCHOR_PITCHES_TEXTCTRL_ID)
        self.Bind(wx.EVT_TEXT,
                  self.OnAPTextChange,
                  self.AnchorPitchesTextCtrl)
        self.AnchorPitchesTextCtrl.SetToolTipString("Input a list of decimals as the "+\
                                                     "Anchor pitches. It must be one "+\
                                                     "longer than the interval pattern.")
        APTextSizer.Add(self.AnchorPitchesTextCtrl)
        sizer.Add(APTextSizer)
        sizer.AddSpacer(20)
        
        ##The line where you define default value of epsilon.
        ESizer=wx.BoxSizer(wx.HORIZONTAL)
        ESizer.AddSpacer(30)
        ESizer.Add(wx.StaticText(self,label="epsilon"))
        ESizer.AddSpacer(5)
        self.EpsilonTextCtrl=wx.TextCtrl(self,size=(45,20),
                                         id=EPSILON_TEXTCTRL_ID)
        self.Bind(wx.EVT_TEXT,
                  self.OnEpsilonUpdate,
                  self.EpsilonTextCtrl)
        self.EpsilonTextCtrl.SetValue('0.4')
        ESizer.Add(self.EpsilonTextCtrl)
        sizer.Add(ESizer)

        sizer.AddSpacer(40)

        ##This line defines the 'create spectrum' and 'load spectrum' buttons
        CLSizer=wx.BoxSizer(wx.HORIZONTAL)
        CLSizer.AddSpacer(30)
        self.CreateSpectrumButton=wx.Button(self,label="Create Spectrum",
                                            id=CREATE_SPECTRUM_BUTTON_ID)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickCreateSpectrum,
                  self.CreateSpectrumButton)
        CLSizer.Add(self.CreateSpectrumButton)
        CLSizer.AddSpacer(20)
        self.LoadSpectrumButton=wx.Button(self,label="Load Spectrum",
                                          id=LOAD_SPECTRUM_ID)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickLoadSpectrum,
                  self.LoadSpectrumButton)
        CLSizer.Add(self.LoadSpectrumButton)
        sizer.Add(CLSizer)

        sizer.AddSpacer(10)
        
        
        ##The line where you define the default spectrum.
        SSizer=wx.BoxSizer(wx.HORIZONTAL)
        SSizer.AddSpacer(30)
        SSizer.Add(wx.StaticText(self,label="choose spectrum"))
        self.SpectrumComboBox=wx.ComboBox(self,choices=['Kkwaengwari',
                                                        'Janggu',
                                                        'Jing',
                                                        'Buk',
                                                        'Pyeongyeong',
                                                        'Korean Cicada',
                                                        'Harmonic 3-limit',
                                                        'Harmonic 5-limit',
                                                        'Harmonic 7-limit',
                                                        'Harmonic 9-limit',
                                                        'Harmonic 11-limit',
                                                        'Harmonic 13-limit',
                                                        'Harmonic 15-limit',
                                                        'Ideal Membrane',
                                                        'Ideal Bar'],
                                          size=(180,25),
                                          id = SPECTRUM_COMBOBOX_ID)
        self.Bind(wx.EVT_COMBOBOX,
                  self.OnSelectSpectrum,
                  self.SpectrumComboBox)
        self.SpectrumComboBox.SetValue('Harmonic 11-limit')
        SSizer.Add(self.SpectrumComboBox)
        sizer.Add(SSizer)

        sizer.AddSpacer(40)

        ##the 'done' and 'cancel' button line.
        DCSizer=wx.BoxSizer(wx.HORIZONTAL)
        DCSizer.AddSpacer(30)
        self.DoneButton=wx.Button(self,label="Done",
                                  id=DONE_BUTTON_ID)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickDone,
                  self.DoneButton)
        DCSizer.Add(self.DoneButton)
        DCSizer.AddSpacer(80)
        self.CancelButton=wx.Button(self, id=CANCEL_ADDNOTES_BUTTON_ID, label="Cancel")
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickCancel,
                  self.CancelButton)
        DCSizer.Add(self.CancelButton)
        sizer.Add(DCSizer)


        self.SetSizer(sizer)

    def OnIntervalPatternUpdate(self,event):
        """Propagates the event to the tuning frame so it can create
        the correct notes."""
        event.Skip()

    def OnRootNoteUpdate(self,event):
        """Propagates the event to the tuning frame so it can create
        the correct notes."""
        event.Skip()
        
    def OnIPBoxChange(self, event):
        """Propagates the event to the tuning frame so it can create
        the values for initial pitches."""
        if self.InitialPitchesCB.GetValue():
            self.InitialPitchesTextCtrl.SetValue('')
            self.InitialPitchesTextCtrl.Disable()
        else:
            self.InitialPitchesTextCtrl.Enable()
        event.Skip()

    def OnIPTextChange(self, event):
        if self.InitialPitchesTextCtrl.GetValue != '':
            self.InitialPitchesCB.SetValue(False)
            
    def OnAPBoxChange(self, event):
        if self.AnchorPitchesCB.GetValue():
            self.AnchorPitchesTextCtrl.SetValue('')
            self.AnchorPitchesTextCtrl.Disable()
        else:
            self.AnchorPitchesTextCtrl.Enable()
        event.Skip()

    def OnAPTextChange(self, event):
        if self.AnchorPitchesTextCtrl.GetValue != '':
            self.AnchorPitchesCB.SetValue(False)

    def OnEpsilonUpdate(self,event):
        event.Skip

    def OnClickCreateSpectrum(self, event):
        newFrame = CreateSpectrumFrame(self)
        newFrame.Show()
        event.Skip()
    
    def OnClickLoadSpectrum(self, event):
        self.DoLoadSpectrum()
        event.Skip()

    def DoLoadSpectrum(self):
        wildcard = "Spectrum Files (*.spc)|*.spc"
        dlg = wx.FileDialog(self,
                            message="Load Spectrum File",
                            wildcard=wildcard,
                            style=wx.FD_OPEN,
                            defaultDir=app.config.GetUserConfigPath("Spectra/User Spectra"))
        if dlg.ShowModal() == wx.ID_OK:
            path = dlg.GetPath()
            with open(path, "rb") as handle:
                exec(handle.read())
##                self.name = spectrumName
##                self.PartialList = partialList
##                self.AmplitudeList = amplitudeList
            spectrumName = basename(path).strip('.spc')
            self.SpectrumComboBox.Append(spectrumName)
            self.SpectrumComboBox.SetValue(spectrumName)
                
        dlg.Destroy()
    
    def OnSelectSpectrum(self,event):
        event.Skip()

    def OnClickDone(self, event):
        intervalPatternLen = len(self.IntervalPatternTextCtrl.GetValue().split())
        if not self.InitialPitchesCB.GetValue():
            InitialPitchesStringList=self.InitialPitchesTextCtrl.GetValue().split()
            if len(InitialPitchesStringList) != intervalPatternLen+1:
                wx.MessageBox("Initial pitches list must be one longer than the interval pattern",
                                   style=wx.CENTER|wx.ICON_ERROR|wx.OK)
                return False
            try:
                a = [float(x) for x in InitialPitchesStringList]
            except:
                wx.MessageBox("Initial pitches list must be numbers separated by spaces",
                                   style=wx.CENTER|wx.ICON_ERROR|wx.OK)
                return False
            
        if not self.AnchorPitchesCB.GetValue():
            AnchorPitchesStringList=self.AnchorPitchesTextCtrl.GetValue().split()
            if len(AnchorPitchesStringList) != intervalPatternLen+1:
                wx.MessageBox("Anchor pitches list must be one longer than the interval pattern",
                                   style=wx.CENTER|wx.ICON_ERROR|wx.OK)
                return False
            try:
                a = [float(x) for x in AnchorPitchesStringList]
            except:
                wx.MessageBox("Anchor pitches list must be numbers separated by spaces",
                                   style=wx.CENTER|wx.ICON_ERROR|wx.OK)
                return False

        try:
            a=float(self.EpsilonTextCtrl.GetValue())
        except:
            wx.MessageBox("Epsilon must be a number.",
                                   style=wx.CENTER|wx.ICON_ERROR|wx.OK)
            return False
        
        event.Skip()

    def OnClickCancel(self, event):
        self.Hide()

     

class TuningFrame(PersistentFrame):
    """The main frame in which the user interacts."""
    def __init__(self, parent, id=wx.ID_ANY, title="Untitled Tuning",
                 pos=wx.DefaultPosition, size = (1300,800),
                 style=wx.DEFAULT_FRAME_STYLE,
                 name="TuningFrame"):
        super(TuningFrame,self).__init__(parent,id,title,
                                         pos,size,style,name)

        
        #Attributes
        self.tuning = tuning()
        self.AddNotesFrame=True
        self.file = None
        self.dotTunFile = None
        
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self.sizer.AddSpacer(20)
        self.Bind(wx.EVT_BUTTON, self.handle_EVT)
        self.Bind(wx.EVT_COMBOBOX, self.handle_EVT)
        self.Bind(wx.EVT_TEXT, self.handle_EVT)
        self.Bind(wx.EVT_CHECKBOX, self.handle_EVT)
        
    #The "Load Tuning" and "Clear Tuning" button
        ltsizer=wx.BoxSizer(wx.HORIZONTAL)
        ltsizer.AddSpacer(30)
        self.LoadTuningButton = wx.Button(self,
                                      label="Load Tuning",
                                      id=LOAD_TUNING_BUTTON_ID)
        self.sizer.Add(self.LoadTuningButton)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickLoadTuning,
                  self.LoadTuningButton)
        ltsizer.Add(self.LoadTuningButton)

        ltsizer.AddSpacer(60)
        self.ClearTuningButton = wx.Button(self,
                                      label="Clear Tuning",
                                      id=CLEAR_TUNING_BUTTON_ID)
        self.sizer.Add(self.ClearTuningButton)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickClearTuning,
                  self.ClearTuningButton)
        ltsizer.Add(self.ClearTuningButton)

        self.sizer.Add(ltsizer)
        self.sizer.AddSpacer(10)
        
        
    #The "Gauge Panel" which provides feedback on the
    #progress of the tuning and the pitch of each note.
        self.gpsizer=wx.BoxSizer(wx.HORIZONTAL)
        self.gpsizer.AddSpacer(30)
        self.GaugePanel=wx.Panel(self,style=wx.SUNKEN_BORDER)
        self.GaugePanel.SetSize((1000,300))
        self.GaugePanel.SetForegroundColour('RED')
        self.gpsizer.Add(self.GaugePanel)
        self.sizer.Add(self.gpsizer)
        self.sizer.AddSpacer(10)
        

    #The row that lays out the tuning creation workflow:
    #"Add Notes", "Tune Up", "Export .tun File", "Save Tuning."
        tuningActionSizer=wx.BoxSizer(wx.HORIZONTAL)
        tuningActionSizer.AddSpacer(30)

        #"tuning workflow -->" text display.
        tuningActionSizer.Add(wx.StaticText(self,-1,"Tuning Workflow -->"))
        tuningActionSizer.AddSpacer(25)
        
        #The "Add Notes" button.
        self.AddNotesButton = wx.Button(self,label="Add Notes",id=ADD_BUTTON_ID)
        self.AddNotesButton.SetFocus()
        tuningActionSizer.Add(self.AddNotesButton)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickAddNotes,
                  self.AddNotesButton)


        tuningActionSizer.AddSpacer(60)


        #The "Tune up" button
        self.TuneUpButton = wx.Button(self,
                                      label="Tune Up",
                                      id=TUNE_UP_BUTTON_ID)
        tuningActionSizer.Add(self.TuneUpButton)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickTuneUp,
                  self.TuneUpButton)


        tuningActionSizer.AddSpacer(60)

        
        #The "ExportDotTunFile" button.
        self.ExportDotTunFileButton = wx.Button(self,
                                                label="Export .tun File",
                                                id= EXPORT_DOT_TUN_ID)
        tuningActionSizer.Add(self.ExportDotTunFileButton)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickExportDotTunFile,
                  self.ExportDotTunFileButton)

        tuningActionSizer.AddSpacer(60)

        #The "Save Tuning" button
        self.SaveTuningButton = wx.Button(self,
                                      label="Save Tuning",
                                      id=SAVE_TUNING_BUTTON_ID)
        tuningActionSizer.Add(self.SaveTuningButton)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickSaveTuning,
                  self.SaveTuningButton)


                                         
    
        self.sizer.Add(tuningActionSizer)
        


    #the row that furnishes analysis of the tunings.
        tuningAnalysisSizer=wx.BoxSizer(wx.HORIZONTAL)
        tuningAnalysisSizer.AddSpacer(30)

        #"Tuning Analysis -->" text.
        tuningAnalysisSizer.Add(wx.StaticText(self,-1,"Tuning Analysis -->"))
        tuningAnalysisSizer.AddSpacer(25)
        
        #The "Interval Table" button
        self.IntervalTableButton = wx.Button(self,
                                             label="Interval Table",
                                             id=INTERVAL_TABLE_ID)
        tuningAnalysisSizer.Add(self.IntervalTableButton)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickIntervalTable,
                  self.IntervalTableButton)


        tuningAnalysisSizer.AddSpacer(100)

        
        #The "Cliques" button
        self.CliquesButton = wx.Button(self,
                                      label="Cliques",
                                      id=CLIQUES_BUTTON_ID)
        tuningAnalysisSizer.Add(self.CliquesButton)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickCliques,
                  self.CliquesButton)

        tuningAnalysisSizer.AddSpacer(100)

        self.sizer.Add(tuningAnalysisSizer)

    #the row for generating melodies and chords from the structure of the tuning.
        generateSizer=wx.BoxSizer(wx.HORIZONTAL)
        generateSizer.AddSpacer(30)

        #"Generate -->" text.
        generateSizer.Add(wx.StaticText(self,-1,"Generate -->"))
        generateSizer.AddSpacer(60)

        #The "Generate Melody" button
        self.GenerateMelodyButton = wx.Button(self,
                                        label="Generate Melody",
                                        id=GENERATE_MELODY_BUTTON_ID)
        generateSizer.Add(self.GenerateMelodyButton)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickGenerateMelody,
                  self.GenerateMelodyButton)

        generateSizer.AddSpacer(100)

        #The "Generate Chords" button
        self.GenerateChordsButton = wx.Button(self,
                                        label="Generate Chords",
                                        id=GENERATE_CHORDS_BUTTON_ID)
        generateSizer.Add(self.GenerateChordsButton)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickGenerateChords,
                  self.GenerateChordsButton)




        generateSizer.AddSpacer(100)

        #The "Generate First Order" button
        self.GenerateFirstOrderButton = wx.Button(self,
                                        label="Generate First Order",
                                        id=GENERATE_FIRST_ORDER_BUTTON_ID)
        generateSizer.Add(self.GenerateFirstOrderButton)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickGenerateFirstOrder,
                  self.GenerateFirstOrderButton)



        generateSizer.AddSpacer(100)

        #The "Generate Bombs" button
        self.GenerateBombsButton = wx.Button(self,
                                        label="Generate Bombs",
                                        id=GENERATE_BOMBS_BUTTON_ID)
        generateSizer.Add(self.GenerateBombsButton)
        self.Bind(wx.EVT_BUTTON,
                  self.OnClickGenerateBombs,
                  self.GenerateBombsButton)

        self.sizer.Add(generateSizer)
        
        self.SetSizer(self.sizer)


    def handle_EVT(self,event):
        """handles events coming from the children and grandchildren frames"""
        id = event.GetId()
        if id == DONE_BUTTON_ID:
            rootNote=int(self.FindWindowById(ROOT_NOTE_TEXTCTRL_ID).GetValue())
            intervalPattern=[int(x) for x in self.FindWindowById(INTERVAL_PATTERN_TEXTCTRL_ID).GetValue().split()]
            noteList = [sum(intervalPattern[:n],rootNote) for n in range(len(intervalPattern)+1)]
            
            ipCB = self.FindWindowById(INITIAL_PITCHES_CB_ID).GetValue()
            if ipCB:
                initialPitches = noteList
            else:
                initialPitches = [float(x) for x in self.FindWindowById(INITIAL_PITCHES_TEXTCTRL_ID).GetValue().split()]
            apCB = self.FindWindowById(ANCHOR_PITCHES_CB_ID).GetValue()
            if apCB:
                anchorPitches = noteList
            else:
                anchorPitches = [float(x) for x in self.FindWindowById(ANCHOR_PITCHES_TEXTCTRL_ID).GetValue().split()]

            epsilon=float(self.FindWindowById(EPSILON_TEXTCTRL_ID).GetValue())

            spectrumName=self.FindWindowById(SPECTRUM_COMBOBOX_ID).GetValue()
            
            try:
                spectrumFile=app.spectraPath+'/Factory Spectra/'+spectrumName+'.spc'
                exec open(spectrumFile).read()
            except:
                spectrumFile=app.spectraPath+'/User Spectra/'+spectrumName+'.spc'
                exec open(spectrumFile).read()
                
            
            for n in range(len(noteList)):
                self.tuning.AddNote(noteList[n],
                                         initialPitches[n],
                                         anchorPitches[n],
                                         epsilon,
                                         spectrumName,
                                         partialList,
                                         amplitudeList)
            self.tuning.refreshConsonanceScore()

            self.makeGaugePanel()


            self.AddNotesFrame.Destroy()

    def OnClickLoadTuning(self,event):
        wildcard = "Tuning Files (*.tng)|*.tng"
        dlg = wx.FileDialog(self,
                            message="Load Tuning File",
                            wildcard=wildcard,
                            style=wx.FD_OPEN,
                            defaultDir=app.config.GetUserConfigPath("Tunings"))
        if dlg.ShowModal() == wx.ID_OK:
            path = dlg.GetPath()
            with open(path, "rb") as handle:
                exec(handle.read())
            self.SetTitle(self.tuning.name)
            self.makeGaugePanel()
        
            

    def OnClickClearTuning(self,event):
        self.tuning=tuning()
        self.SetTitle(self.tuning.name)
        self.GaugePanel.vsizer.DeleteWindows()
        self.FindWindowById(GAUGE_LINE_ID).Destroy()
        
        

    def OnClickAddNotes(self,event):
        self.AddNotesFrame = AddNotesFrame(parent = self)
        self.AddNotesFrame.Show()

    def OnClickTuneUp(self,event):
        self.tuning.tuneUp()

    def OnClickExportDotTunFile(self,event):

        #Make sure there are at least two notes.
        nn = sorted(self.tuning.coreNotes.keys())
        if len(nn)<2:
            wx.MessageBox("""You must add at least two notes before you
                          can cycle and export to .tun""",
                          style=wx.CENTER|wx.ICON_ERROR|wx.OK)
            return False

        if not self.tuning.cycled:
            self.tuning.cycle()
                    
        #Find out if a .tun file has been saved for this tuning already.
        #If it has, save it immediately. if not, save as. 
        if self.dotTunFile:
            self.DoExportDotTun(self.DotTunFile)
        else:
            self.DoExportDotTunAs()

    def DoExportDotTunAs(self):
        wildcard = ".tun files (*.tun)|*.tun"
        dlg = wx.FileDialog(self,message="Export .tun File As",
                            wildcard=wildcard,
                            style=wx.FD_SAVE|wx.FD_OVERWRITE_PROMPT,
                            defaultDir=app.config.GetUserConfigPath("Dot Tun Files"))
        if dlg.ShowModal() == wx.ID_OK:
            path=dlg.GetPath().strip('.tun')
            self.tuning.name=(basename(path))
            self.file=path+'.tun'
            self.SetTitle(basename(path))
            self.DoExportDotTun(path+'.tun')
            self.DoExportDotTun('/Library/Application Support/Camel Audio/Alchemy/Libraries/Tuning/Dot Tun Files/'+self.tuning.name+'.tun') 
            
            
        dlg.Destroy()


    def DoExportDotTun(self,path):
    
        #Write the dot tun file. 
        f = file(path,mode = 'w')
        
        f.write('; 1. VAZ-section with tunings quantized to integers\n')
        f.write('[Tuning]\n')
        for i in range(128):
            if self.tuning.cycledNotes[i]:
                intFreq = int(100 * (self.tuning.cycledNotes[i].pitch))
                entry = 'note '+str(i)+'='+str(intFreq)+'\n'
            else:
                entry = 'note '+str(i)+'=0\n'
            f.write(entry)

        f.write('; 2. AnaMark-specific section with exact tunings\n')
        f.write('[Exact Tuning]\n')
        for i in range(128):
            if self.tuning.cycledNotes[i]:
                freq = 100 * (self.tuning.cycledNotes[i].pitch)
                entry = 'note '+str(i)+'='+str(freq)+'\n'
            else:
                entry = 'note '+str(i)+'=0\n'
            f.write(entry)
                 
        f.close()
 

    def OnClickIntervalTable(self,event):
        self.DoIntervalTable()

    def OnClickCliques(self,event):
        n = 1
        for c in self.tuning.coreCliques:
            notes = sorted(list(c.midinums))
            CF = CliqueFrame(self)
            CF.cliqueNotes = notes
            if c.quality:
                qtext = ', '+c.quality
            else:
                qtext = ', mixed'
            CF.SetTitle(self.GetTitle()+': Clique '+str(n)+qtext)
            n+=1
            CF.Show()
        notes=sorted(app.TuningFrame.tuning.coreNotes.keys())
        CF=CliqueFrame(self)
        CF.cliqueNotes=notes
        CF.SetTitle(self.GetTitle()+': All Notes')
        CF.Show()

    def OnClickGenerateMelody(self,event):
        self.tuning.generateMelody(2)

    def OnClickGenerateChords(self,event):
        self.tuning.generateChords(32)
        
    def OnClickGenerateFirstOrder(self,event):
        self.tuning.generateFirstOrder(32)            
            
    def OnClickGenerateBombs(self,event):
        """Carries out the generateBombs() function."""
        self.tuning.generateBombs(32)

    def OnClickSaveTuning(self,event):
        """Decides whether to save or save as."""
        evt_id = event.GetId()
        if evt_id == wx.ID_SAVE:
            if self.file:
                self.DoSaveTuning(self.file)
            else:
                self.DoSaveTuningAs()
        else:
            self.DoSaveTuningAs()

    def DoSaveTuningAs(self):
        """Gets the filename and path at which to save a tuning file."""
        wildcard = "Tuning Files (*.tng)|*.tng"
        dlg = wx.FileDialog(self,message="Save Tuning As",
                            wildcard=wildcard,
                            style=wx.FD_SAVE|wx.FD_OVERWRITE_PROMPT,
                            defaultDir=app.config.GetUserConfigPath("Tunings"))
        if dlg.ShowModal() == wx.ID_OK:
            path=dlg.GetPath().strip('.tng')
            self.file=path+'.tng'
            self.SetTitle(basename(path))
            self.DoSaveTuning(path+'.tng')
            self.tuning.name=(basename(path))
        dlg.Destroy()


    def DoSaveTuning(self,path):
        """Saves the tuning in a proprietary format."""
        t = self.tuning
        name = self.GetTitle()
        nn=t.coreNotes.keys()

        tuningFileText=''
        tuningFileText+="self.tuning = tuning()\n"+\
                         "self.tuning.name='"+name+"'\n"
        for n in nn:
            tuningFileText+="self.tuning.AddNote("+str(n)+","+\
                             str(t.coreNotes[n].pitch)+","+\
                             str(t.coreNotes[n].anchorPitch)+","+\
                             str(t.coreNotes[n].epsilon)+","+\
                             "'"+str(t.coreNotes[n].spectrum.spectrumName)+"',"+\
                             str(t.coreNotes[n].spectrum.partialList)+","+\
                             str(t.coreNotes[n].spectrum.amplitudeList)+")\n"
        tuningFileText+="self.tuning.refreshConsonanceScore()\n"
        tuningFileText+="self.tuning.coreConsonanceDict=self.tuning.makeConsonanceDict(self.tuning.coreNotes)[0]\n"
        tuningFileText+="self.tuning.makeIntervalPossibilities()\n"
        tuningFileText+="self.tuning.coreIntervalDict=self.tuning.makeIntervalDict(self.tuning.coreNotes)\n"
        tuningFileText+="self.tuning.coreGraph=self.tuning.makeGraph(self.tuning.coreNotes,self.tuning.coreConsonanceDict)\n"
        tuningFileText+="self.tuning.coreCliques=self.tuning.findCliques(self.tuning.coreGraph,self.tuning.coreNotes,self.tuning.coreIntervalDict)\n"
        with open(path,"wb") as handle:
            handle.write(tuningFileText)

            
    def makeGaugePanel(self):
        """Displays and keeps current gauges for each note. The gauges show the deviation
        between the note's exact pitch and its anchor pitch."""
        
        noteList = sorted(self.tuning.coreNotes.keys())
        self.GaugePanel.vsizer = wx.BoxSizer(wx.VERTICAL)
        self.GaugePanel.vsizer.AddSpacer(90)
        hGaugeSizer = wx.BoxSizer(wx.HORIZONTAL)
        hGaugeSizer.AddSpacer(60)

        #Get rid of any old midinum labels before writing the new ones.
        for n in noteList:
            try:
                exec "self.MidinumLabel"+str(n)+".Destroy()"
            except:
                pass   

        #For each active note, make a gauge graphically showing its current
        #pitch along with a label for the midinum, and another for the current
        #pitch as a decimal number.

        spectrumList=[]
        for n in noteList:
            note = app.TuningFrame.tuning.coreNotes[n]
            if note.spectrum.spectrumName not in spectrumList:
                spectrumList.append(note.spectrum.spectrumName)
            ##one vertical pixel for each cent in the range of pitches allowed for the note.
            if note.epsilon <0.4:
                vertGaugeSize = note.epsilon * 200
            else:
                vertGaugeSize = 80
            ##Center the gauge at 80 pixels from the top of the frame
            s = int(50+(30-(0.5*vertGaugeSize)))
            ##Add midinum labels, gauges, and pitch textctrls for each added note. 
            exec "vGaugeSizer"+str(n)+" = wx.BoxSizer(wx.VERTICAL)"
            exec "vGaugeSizer"+str(n)+".AddSpacer(s)"
            nudgeSizer = wx.BoxSizer(wx.HORIZONTAL)
            nudgeSizer.AddSpacer(15)
            exec "self.MidinumLabel"+str(n)+"=wx.StaticText(self,label='"+str(n)+"')"
            exec "nudgeSizer.Add(self.MidinumLabel"+str(n)+")"
            exec "vGaugeSizer"+str(n)+".Add(nudgeSizer)"
            exec "vGaugeSizer"+str(n)+".AddSpacer(9)"
            nudgeSizer = wx.BoxSizer(wx.HORIZONTAL)
            nudgeSizer.AddSpacer(17)
            exec "GAUGE"+str(n)+"_ID = wx.NewId()"
            exec "self.GaugePanel.Gauge"+str(n)+"= wx.Gauge(self,style=wx.GA_VERTICAL,id=GAUGE"+str(n)+"_ID,size=(0,vertGaugeSize))"
            value = int(round((note.pitch-note.anchorPitch)*100))+vertGaugeSize/2
            exec "self.GaugePanel.Gauge"+str(n)+".SetValue("+str(100*value/vertGaugeSize)+")"
            exec "nudgeSizer.Add(self.GaugePanel.Gauge"+str(n)+")"
            exec "vGaugeSizer"+str(n)+".Add(nudgeSizer)"
            exec "vGaugeSizer"+str(n)+".AddSpacer(9)"
            exec "self.GaugePanel.PitchDisplay"+str(n)+"=wx.TextCtrl(self,size=(50,20),style=wx.TE_READONLY|wx.BORDER_NONE|wx.TE_RICH2,value='"+str(float(note.pitch))+"')"
            exec "vGaugeSizer"+str(n)+".Add(self.GaugePanel.PitchDisplay"+str(n)+")"
            exec "hGaugeSizer.Add(vGaugeSizer"+str(n)+")"
            hGaugeSizer.AddSpacer(10)
    

        wx.StaticLine(self,GAUGE_LINE_ID,pos=(50,193),size=(len(noteList)*60,5),style=wx.LI_HORIZONTAL)
        #The Spectrum Display
        self.GaugePanel.vsizer.Add(hGaugeSizer)
        self.GaugePanel.vsizer.AddSpacer(30)
        nudgeSizer = wx.BoxSizer(wx.HORIZONTAL)
        nudgeSizer.AddSpacer(60)
        self.spectrumDisplay=wx.StaticText(self,-1,"Spectrum: "+'\n'.join(spectrumList))
        nudgeSizer.Add(self.spectrumDisplay)
        self.GaugePanel.vsizer.Add(nudgeSizer)
       
        #The Aligned Partials and Consonance Score displays.
        nudgeSizer = wx.BoxSizer(wx.HORIZONTAL)
        nudgeSizer.AddSpacer(60)
        self.AlignedPartialsTextCtrl=wx.TextCtrl(self,value=str(self.tuning.AlignedPartials))
        nudgeSizer.Add(wx.StaticText(self,-1,"Aligned Partials:"))
        nudgeSizer.AddSpacer(10)
        nudgeSizer.Add(self.AlignedPartialsTextCtrl)
        nudgeSizer.AddSpacer(60)
        self.ConsonanceScoreTextCtrl=wx.TextCtrl(self,value=str(self.tuning.ConsonanceScore))
        nudgeSizer.Add(wx.StaticText(self,-1,"Consonance Score:"))
        nudgeSizer.AddSpacer(10)
        nudgeSizer.Add(self.ConsonanceScoreTextCtrl)
        self.GaugePanel.vsizer.Add(nudgeSizer)
        self.GaugePanel.SetSizer(self.GaugePanel.vsizer)
        self.GaugePanel.Layout()


    def DoIntervalTable(self):
        """This function puts together the interval table and makes it visible."""
        self.IntervalTableFrame = IntervalTableFrame(self)
        self.IntervalTableFrame.intervalTableNotes = sorted(self.tuning.coreNotes.keys())
        self.IntervalTableFrame.SetTitle(self.GetTitle()+' intervals')
        self.IntervalTableFrame.setupTable()
        self.IntervalTableFrame.Show()


            
        
    
        
class TuningApp(wx.App):
    """This is the app object that is created by the main loop."""
    def OnInit(self):
        self.SetAppName("Spectral Tuner")
        
        ##This block checks if the "Factory Spectra" directory exists.
        ##If not, it installs all the necessary directories on the user's computer.
        self.config = ConfigHelper()
        if not self.config.HasConfigFile("Spectra/Factory Spectra"):
            self.config.CreateUserCfgDir("Spectra/Factory Spectra")
            self.config.CreateUserCfgDir("Spectra/User Spectra")
            self.config.CreateUserCfgDir("Tunings")
            self.config.CreateUserCfgDir("Dot Tun Files")
            installFactoryFiles.InstallFactorySpectraFiles(self.config.GetUserConfigPath("Spectra/Factory Spectra"))
        self.spectraPath=self.config.GetUserConfigPath("Spectra")
        self.tuningsPath=self.config.GetUserConfigPath("Tunings")
                                                                                      
                                                    
        ##Here, the tuning frame is initiated. 
        self.TuningFrame = TuningFrame(None)
        self.TuningFrame.Show()
        return True
    

    


###Here's the main loop, which makes the whole program go.
if __name__ =="__main__":
    app = TuningApp(False)
    SCREEN_X,SCREEN_Y=wx.DisplaySize()
    app.MainLoop()














   



      






