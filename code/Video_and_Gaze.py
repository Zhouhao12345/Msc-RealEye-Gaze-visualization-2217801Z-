#!/usr/bin/python
# vim: tabstop=8 expandtab shiftwidth=4 softtabstop=4

""" Video Syncing with Gaze data overlay
"
" This example uses the video as a main source to sync eyetracking data. Since the
" video is the main source the eyetracking data will be synced on the videos output.
"
" Eyetracking data is read directly into eyetracking data queues (one sync and one data)
"
" When a video pts is detected on the incoming data it is added with the buffer
" offset.
"
" When a video is about to be displayed its offset is matched with the offset
" in the video pts queue to get the corresponding pts. With this pts we can
" calculate the pts sync point in the eyetracking data and present the
" yetracking points that corresponds to this pts. For frames without pts we
" move eyetracking data forward using the video frame timestamps.
"
" Note: This example program is *only* tested with Python 2.7 on Ubuntu 12.04 LTS  
"       and Ubuntu 14.04 LTS (running natively).
"""

# Standard libraries. We need socket for socket communication and json for
# json parsing
import socket
import json
import sys, os, gobject
from Tkinter import *
import Image, ImageTk
import numpy as np
import math
import threading
import tkFileDialog
import tkMessageBox
import select
import os.path
import sys
import time

# GStreamer integration. We need glib for main loop handling and gst for
# gstreamer video.



try:
    import glib
    import gst
    from ar_markers.hamming.detect import detect_markers
    import cv2
    import pygame

except ImportError:
    print "Please make sure you have glib,pygame, gst, cv2, and ar_markers python integration installed"
    raise

# Model Class: Get video stream and data stream from Tobii Glasses Recording Unit 
# {
def mksock(peer):
    """ Create a socket pair for a peer description """
    iptype = socket.AF_INET
    if ':' in peer[0]:
        iptype = socket.AF_INET6
    return socket.socket(iptype, socket.SOCK_DGRAM)

class KeepAlive:
    """ Sends keep-alive signals to a peer via a socket """
    _sig = 0
    def __init__(self, sock, peer, streamtype, timeout=1):
        jsonobj = json.dumps({
            'op' : 'start',
            'type' : ".".join(["live", streamtype, "unicast"]),
            'key' : 'anything'})
        sock.sendto(jsonobj, peer)
        self._sig = glib.timeout_add_seconds(timeout, self._timeout, sock, peer, jsonobj)

    def _timeout(self, sock, peer, jsonobj):
        sock.sendto(jsonobj, peer)
        return True

    def stop(self):
        glib.source_remove(self._sig)


class BufferSync():
    """ Handles the buffer syncing
    "
    " When new eyetracking data arrives we store it in a et queue and the 
    " specific eyetracking to pts sync points in a et-pts-sync queue.
    "
    " When MPegTS is decoded we store pts values with the decoded offset in a
    " pts queue.
    "
    " When a frame is about to be displayed we take the offset and match with
    " the pts from the pts queue. This pts is then synced with the
    " et-pts-sync queue to get the current sync point. With this sync point
    " we can sync the et queue to the video output.
    "
    " For video frames without matching pts we move the eyetracking data forward
    " using the frame timestamps.
    " 
    """
    _et_syncs = []      # Eyetracking Sync items
    _et_queue = []      # Eyetracking Data items
    _et_ts = 0          # Last Eyetraing Timestamp
    _pts_queue = []     # Pts queue
    _pts_ts = 0         # Pts timestamp

    def __init__(self, cb):
        """ Initialize a Buffersync with a callback to call with each synced
        " eyetracking data
        """
        self._callback = cb

    def add_et(self, obj):
        """ Add new eyetracking data point """
        # Store sync (pts) objects in _sync queue instead of normal queue
        if 'pts' in obj:
            self._et_syncs.append(obj)
        else:
            self._et_queue.append(obj)

    def sync_et(self, pts, timestamp):
        """ Sync eyetracking sync datapoints against a video pts timestamp and stores
        " the frame timestamp
        """
        # Split the gaze syncs to ones before pts and keep the ones after pts
        syncspast = filter(lambda x: x['pts'] <= pts, self._et_syncs)
        self._et_syncs = filter(lambda x: x['pts'] > pts, self._et_syncs)
        if syncspast != []:
            # store last sync time in gaze ts and video ts
            self._et_ts = syncspast[-1]['ts']
            self._pts_ts = timestamp

    def flush_et(self, timestamp):
        """ Flushes synced eyetracking on video
        " This calculates the current timestamp with the last gaze sync and the video
        " frame timestamp issuing a callback on eyetracking data that match the
        " timestamps.
        """
        nowts = self._et_ts + (timestamp - self._pts_ts)
        # Split the eyetracking queue into passed points and future points
        passed = filter(lambda x: x['ts'] <= nowts, self._et_queue)
        self._et_queue = filter(lambda x: x['ts'] > nowts, self._et_queue)
        # Send passed to callback
        self._callback(passed)

    def add_pts_offset(self, offset, pts):
        """ Add pts to offset queue """
        self._pts_queue.append((offset, pts))

    def flush_pts(self, offset, timestamp):
        """ Flush pts to offset or use timestamp to move data forward """
        # Split pts queue to used offsets and past offsets
        used = filter(lambda x: x[0] <= offset, self._pts_queue)
        self._pts_queue = filter(lambda x: x[0] > offset, self._pts_queue)
        if used != []:
            # Sync with the last pts for this offset
            self.sync_et(used[-1][1], timestamp)
        self.flush_et(timestamp)


class EyeTracking():
    """ Read eyetracking data from RU """
    _ioc_sig = 0
    _buffersync = None
    def start(self, peer, buffersync):
        self._sock = mksock(peer)
        self._keepalive = KeepAlive(self._sock, peer, "data")
        ioc = glib.IOChannel(self._sock.fileno())
        self._ioc_sig = ioc.add_watch(glib.IO_IN, self._data)
        self._buffersync = buffersync

    def _data(self, ioc, cond):
        """ Read next line of data """
        self._buffersync.add_et(json.loads(ioc.readline()))
        return True
   
    def stop(self):
        """ Stop the live data """
        self._keepalive.stop()
        self._sock.close()
        glib.source_remove(self._ioc_sig)


class Video():
    """ Video stream from RU """
    _PIPEDEF=[
        "udpsrc name=src", # UDP video data
        "tsparse",                      # parse the incoming stream to MPegTS
        "tsdemux emit-stats=True",      # get pts statistics from the MPegTS stream
        "tee name=t",
        "queue2",                        # build queue for the decoder
        "ffdec_h264 max-threads=0",     # decode the incoming stream to frames
        "identity name=decoded",        # used to grab video frame to be displayed
        "textoverlay name=textovl text=o halignment=position valignment=position xpad=0  ypad=0", # simple text overlayz
        "xvimagesink force-aspect-ratio=True name=video t.", # Output on XV video
        "queue2",
        "h264parse",
        "rtph264pay config-interval=1 pt=96",
        "udpsink host=127.0.0.1 port=5000"
    ]
    _pipeline = None    # The GStreamer pipeline
    _textovl = None     # Text overlay element
    _keepalive = None   # Keepalive for video
    _sock = None        # Communicaion socket


    def draw_gaze(self, objs):
        """ Move gaze point on screen """
        # Filter out gaze points. Gaze comes in higher Hz then video so there
        # should be 1 to 3 gaze points for each video frame
        global gazepoint
        objs = filter(lambda x: 'gp' in x, objs)
        if len(objs) > 3:
            print "Drop %d" % len(objs)
        if len(objs) == 0:
            return
        obj = objs[-1]
        if 'gp' in obj and obj['gp'][0] != 0 and obj['gp'][1] != 0:
            self._textovl.set_property("xpos", obj['gp'][0])
            self._textovl.set_property("ypos", obj['gp'][1])
        gazepoint=(obj['gp'][0],obj['gp'][1])
        #(xpos,ypos)=(0,0) top,left  (1,1) bot,right

    def start(self, peer, buffersync):
        """ Start grabbing video """
        # Create socket and set syncbuffer
        self._sock = mksock(peer)
        self._buffersync = buffersync

        # Create pipeline
        self._pipeline=gst.parse_launch(" ! ".join(self._PIPEDEF))


        # Add watch to pipeline to get tsdemux messages
        bus = self._pipeline.get_bus()
        bus.add_watch(self._bus)
        bus.enable_sync_message_emission()
        bus.connect("message", self.on_message)
        bus.connect("sync-message::element", self.on_sync_message)
         #Set socket to get data from out socket
        src = self._pipeline.get_by_name("src")
        src.set_property("sockfd", self._sock.fileno())

        # Catch decoded frames
        decoded = self._pipeline.get_by_name("decoded")
        decoded.connect("handoff", self._decoded_buffer)

        # Store overlay object
        self._textovl = self._pipeline.get_by_name("textovl")

        # Start video streaming
        self._keepalive = KeepAlive(self._sock, peer, "video")

        # Start the video pipeline
        self._pipeline.set_state(gst.STATE_PLAYING)

    def on_message(self, bus, message):
        t = message.type
        if t == gst.MESSAGE_EOS:
            self._pipeline.set_state(gst.STATE_NULL)
            print "123"
        elif t == gst.MESSAGE_ERROR:
            err, debug = message.parse_error()
            print "Error: %s" % err, debug
            self._pipeline.set_state(gst.STATE_NULL)

    def on_sync_message(self, bus, message):
        if message.structure is None:
            return
        message_name = message.structure.get_name()
        if message_name == "prepare-xwindow-id":
            # Assign the viewport
            imagesink = message.src
            imagesink.set_property("force-aspect-ratio", True)
            imagesink.set_xwindow_id(winid)

    def _bus(self, bus, msg):
        """ Buss message handler
        " We only collect pts-offset pairs
        """
        if msg.type == gst.MESSAGE_ELEMENT:
            st = msg.structure
            # If we have a tsdemux message with pts field then lets store it
            # for the render pipeline. Will be piced up by the handoff
            if st.has_name("tsdemux") and st.has_field("pts"):
                    self._buffersync.add_pts_offset(st['offset'], st['pts'])
        return True

    def _decoded_buffer(self, ident, buf):
        """ Callback for decoded buffer """
        # Make sure to convert timestamp to us
        self._buffersync.flush_pts(buf.offset, buf.timestamp/1000)

    def stop(self):
        self._pipeline.set_state(gst.STATE_NULL)
        self._pipeline = None
        self._sock.close()
        self._sock = None
        self._keepalive.stop()
        self._keepalive = None

# }

# View/Control class: Show GUI, and analyze the user action event
# {
class Prototype(Frame):
    def __init__(self, parent):
        gobject.threads_init()
        Frame.__init__(self, parent)
        global gazepoint
        gazepoint=(0,0)
		self.screenwidth=self.winfo_screenwidth()/2.0
        self.screenheight=self.winfo_screenheight()/2.0
		# get the specific screen size
		
        self.usedx=0
        self.usedy=0
        self.peer = ("192.168.71.50", 49152)
        self.video = Video()
        self.et = EyeTracking()
        self.buffersync = BufferSync(self.video.draw_gaze)
        self.et.start(self.peer, self.buffersync)
        self.video.start(self.peer, self.buffersync)
        # Start video and gaze stream
		
        self.capture=None
        self.parent = parent
        self.parent.title("Gaze_Detect")
        self.parent.geometry(str(int(self.screenwidth*2))+"x"+str(int(self.screenheight*2-88*(self.screenheight*2/768)))+"+0+0")
        self.parent.resizable(width=FALSE, height=FALSE)
		# Main UI 
		
        self.newWindow = Toplevel(self.parent)
        self.camera_frame = Frame(self.newWindow,width=int(self.screenwidth), height=int(self.screenheight), bg="black")
        global winid
        winid=self.camera_frame.winfo_id()
        self.camera_frame.pack()
        self.newWindow.withdraw()
        self.newWindow.protocol("WM_DELETE_WINDOW", self.on_closing)
		# UI for scene camera video, but hidden behind Main UI 

        self.WelWindow = Toplevel(self.parent)
        self.WelWindow.geometry(str(int(self.screenwidth)/2)+"x"+str(int(self.screenheight)/2)+"+200+200")
        self.WelWindow.title("Test your link")
        msg = Message(self.WelWindow, text=self.testlink(),width=int(self.screenheight)/2)
        msg.grid(row=0,column=0)
        inputnamepanel=Frame(self.WelWindow,width=int(self.screenheight)/2)
        inputnamepanel.grid(row=1,column=0)
        text=Label(inputnamepanel, text="Enter your name here",width=int(self.screenheight)/16)
        text.grid(row=0,column=0)
        self.name= Entry(inputnamepanel, text="Enter your name here",width=int(self.screenheight)/32)
        self.name.grid(row=0,column=1)
        button = Button(self.WelWindow, text="Next",command=self.createcameratest)
        button.grid(row=2,column=0)
        self.WelWindow.attributes("-topmost", True)
        self.camera_frame.pack()
        self.changeX=0
        self.changeY=0
        self.point=(0,0)
		# Communication Test UI: test connection between glasses and video installation
		
        menubar = Menu(self.parent)
        fileMenu = Menu(menubar,tearoff=0)
        cameraMenu = Menu(menubar,tearoff=0)
        cameraMenu.add_command(label="Open", command=self.showcamera)
        menubar.add_cascade(label="Camera", menu=cameraMenu)
        checkMenu = Menu(menubar,bg="blue",tearoff=0)
        menubar.add_cascade(label="Check", menu=checkMenu)
        fileMenu.add_command(label="Open", command=self.onOpen)
        menubar.add_cascade(label="File", menu=fileMenu)
        self.parent.config(menu=menubar)
		# Menu for Main UI
		
        self.videoframe = Frame(self, width=int(self.screenwidth*2), height=int(self.screenheight*2-88*(self.screenheight*2/768)),bg="black")
        global videoid
        videoid=self.videoframe.winfo_id()
        self.blurred=False
		# Next test UI prepare

    def on_closing(self):
        self.newWindow.withdraw()



    def createcameratest(self):
        self.username=self.name.get()
        self.capture = cv2.VideoCapture("123.sdp")
		# Build sdp video channel
		
        self.WelWindow.destroy()
		# Communication Test UI Clean
		
		# Marker detection test UI: Detect markers  
        self.Test1Window = Toplevel(self.parent)
        self.Test1Window.geometry(str(int(self.screenwidth))+"x"+str(int(self.screenheight)+50)+"+200+200")
        self.Test1Window.title("Test your view: ")
        self.testoneframe = Frame(self.Test1Window,width=int(self.screenwidth), height=int(self.screenheight), bg="black")
        self.testoneframe.pack(side=TOP,  padx=0, pady=0)
        self.lmain = Label(self.testoneframe)
        self.testoneframe_other = Frame(self.Test1Window,width=int(self.screenwidth), height=50, bg="black")
        self.testoneframe_other.pack(side=BOTTOM,  padx=0, pady=0)
        labe=Label(self.testoneframe_other,text="Change your view and make sure you can view at least two markers around with green ")
        labe.grid(row=0, column=0)
        button2 = Button(self.testoneframe_other, text="Blurred?",command=self.display_as_cvwindow)
        button2.grid(row=0, column=1)
        button = Button(self.testoneframe_other, text="Next",command=self.creategazetest)
        button.grid(row=0, column=2)
		# Frame for Camera Video and Control panel 
		
        self.testframe()
		# Call function to show video frame with markers in loop
		
    def creategazetest(self):

        self.capture.release()
        cv2.destroyAllWindows()
        self.capture = cv2.VideoCapture("123.sdp")
		
        self.lmain.after_cancel(testjob)
		# End loop
		
		# Gaze Calibration UI: Calibrate gaze 
        self.Test1Window.destroy()
        self.Test2Window = Toplevel(self.parent)
        self.Test2Window.geometry(str(int(self.screenwidth)*2)+"x"+str(int(self.screenheight*2))+"+0+0")
        self.Test2Window.title("Test your gaze: ")
        self.Test2Window.resizable(width=FALSE, height=FALSE)
        self.Test2Window_control = Frame(self.Test2Window,width=int(self.screenwidth)*2, height=35*(self.screenheight*2/768))
        self.Test2Window_control.grid(row=0, column=0)
        labe=Label(self.Test2Window_control,text="Your gaze will appear on the black board with small white points,fouse your gaze on the big white point, move the big point to the your gaze point area by click buttons on the right side ")
        labe=labe.grid(row=0,column=0)
        control_frame = Frame(self.Test2Window_control,width=int(self.screenwidth), height=20, bg="black")
        control_frame.grid(row=1,column=0)
        control_leftbut=Button(control_frame,text="Left",command=self.moveleft)
        control_leftbut.grid(row=0,column=0)
        control_rightbut=Button(control_frame,text="Right",command=self.moveright)
        control_rightbut.grid(row=0,column=1)
        control_upbut=Button(control_frame,text="Up",command=self.moveup)
        control_upbut.grid(row=0,column=2)
        control_downbut=Button(control_frame,text="Down",command=self.movedown)
        control_downbut.grid(row=0,column=3)
        refreshbut=Button(control_frame,text="Refresh",command=self.changerefresh)
        refreshbut.grid(row=0,column=4)
        control_nextbut=Button(self.Test2Window_control,text="Next",command=self.next)
        control_nextbut.grid(row=1,column=5)

        self.bigpointX=self.screenwidth
        self.bigpointY=self.screenheight-44*(self.screenheight*2/768)

        self.canvas=Canvas(self.Test2Window,width=int(self.screenwidth)*2, height=int(self.screenheight*2-88*(self.screenheight*2/768)),bg="white")
        self.drawpoint()
        # drawpoint in loop
		
    # Clean all red point on canvas
    def changerefresh(self):
        self.canvas.delete("all")

    # Function to control calibration marker: big black dot
    def moveleft(self):
        self.bigpointX=self.bigpointX-10
    def moveright(self):
        self.bigpointX=self.bigpointX+10
    def moveup(self):
        self.bigpointY=self.bigpointY-10
    def movedown(self):
        self.bigpointY=self.bigpointY+10
    
	# destroy all test UI, launch gaze visible test
    def next(self):
        self.capture.release()
        cv2.destroyAllWindows()
        self.canvas.after_cancel(test2job)
        self.Test2Window.destroy()
        self.changeX=self.screenwidth-self.bigpointX
        self.changeY=self.screenheight-self.bigpointY

    # Gaze calibration test: draw red point on canvas in loop
    def drawpoint(self):
        global test2job
        self.canvas.grid(row=2, column=0)
        self.refresh=False
        self.canvas.delete("ball")
        self.ball=self.canvas.create_oval(self.bigpointX-30,self.bigpointY-30,self.bigpointX+30,self.bigpointY+30,fill="black",outline="black", width=4,tag="ball")
        if self.capture.isOpened(): # try to get the first frame
           frame_captured,frame = self.capture.read()
        else:
           frame_captured = False
        img2=cv2.resize(frame,(int(self.screenwidth),int(self.screenheight)))
        self.markers = detect_markers(img2)
        for marker in self.markers:
            marker.highlite_marker(img2)
        point=self.gazescreen(self.markers.__len__())
        if self.gazeandmarkers(self.markers.__len__()):
              self.canvas.create_oval(point[0]-2, point[1]-2, point[0]+2, point[1]+2, fill="red", outline="red", width=4)
        test2job=self.canvas.after(1, self.drawpoint)
     
	# Marker detection test: show scene camera video frame in loop
    def testframe(self):
        global testjob
        self.lmain.grid(row=0, column=0)
        if self.capture.isOpened(): # try to get the first frame
           frame_captured,frame = self.capture.read()
        else:
           frame_captured = False
        img2=cv2.resize(frame,(int(self.screenwidth),int(self.screenheight)))
        markers = detect_markers(img2)
        for marker in markers:
            marker.highlite_marker(img2)
        #point=self.gazescreen(self.markers.__len__())
        cv2.putText(img2, str(markers.__len__()),(int(self.screenwidth)-50,50),cv2.FONT_HERSHEY_SIMPLEX, 2, (0, 255, 0), 3)
        im = Image.fromarray(img2)
        imgtk = ImageTk.PhotoImage(image=im)
        self.lmain.imgtk = imgtk
        self.lmain.configure(image=imgtk)
        testjob=self.lmain.after(1, self.testframe)

    # Communication Test: Try to link glasses for 5 seconds
    def testlink(self):
        MULTICAST_ADDR = 'ff02::1'  # ipv6: all nodes on the local network segment
        PORT = 13007
        self.s6 = socket.socket(socket.AF_INET6, socket.SOCK_DGRAM)
        self.s6.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.s6.bind(('::', PORT))

        self.s6.sendto('{"type":"discover"}', (MULTICAST_ADDR, 13006))
        try:
            self.s6.settimeout(5)
            data, address = self.s6.recvfrom(1024)
            test = (" From: " + address[0] + " glasses has been linked" )
        except socket.error:
             if tkMessageBox.showwarning("Warning", "Please check your link with glasses and restart the application"):
                 sys.exit(0)



        return test
	
    # Main UI: build filedialog to select video from file explorer 
    def onOpen(self):
        if self.username!='':
            self.userdetail=str(sys.path[1])+str('/')+str(self.username)
        else:
            self.userdetail=str(sys.path[1])+str('/')+str("Anyone")


        if self.capture.isOpened():
            self.capture.release()
            self.pipeline2.set_state(gst.STATE_NULL)
            self.videoframe.after_cancel(job)
        ftypes = [('All files', '*')]
        dlg = tkFileDialog.Open(self, filetypes = ftypes)
        fl = dlg.show()
        self.str=fl
        if fl != '':
            self.filepath=self.userdetail+str('/')+os.path.basename(fl).replace('.','')
            if os.path.isdir(self.userdetail):
                self.outputfile=open(self.filepath,'w')
            else:
                os.mkdir(self.userdetail)
                self.outputfile=open(self.filepath,'w')
            self.outputfile.write('{ "x" : "0" , "y" : "0" , "ts" : "0" }\n')
			# create documnet to store gaze recording
			
            self.pipeline2 = gst.parse_launch("filesrc name=src ! decodebin2 ! textoverlay name=textovl text=o halignment=position valignment=position xpad=0  ypad=0 ! xvimagesink")
            bus = self.pipeline2.get_bus()
            bus.add_signal_watch()
            bus.enable_sync_message_emission()
            bus.connect("sync-message::element", self.on_sync_message)
            src = self.pipeline2.get_by_name("src")
            src.set_property("location",fl)
            self.textovl = self.pipeline2.get_by_name("textovl")
            self.pipeline2.set_state(gst.STATE_PLAYING)
            self.capture = cv2.VideoCapture("123.sdp")
            self.starttime=time.time()
            self.show_frame()
			# build gst pipeline to show video on Main UI

    def on_sync_message(self,bus, message):
        if message.structure is None:
                return
        message_name = message.structure.get_name()
        if message_name == "prepare-xwindow-id":
                imagesink = message.src
                imagesink.set_property("force-aspect-ratio", True)
                imagesink.set_xwindow_id(videoid)
     
	# show the hidden camera window
    def showcamera(self):
        self.newWindow.update()
        self.newWindow.deiconify()

    # "Is gaze on screen" algorithm
    # {	
    def gazeandmarkers(self,markernum):
        switcher={
            0: self.none,
            1: self.one,
            2: self.two,
            3: self.three,
            4: self.four,
        }
        func = switcher.get(markernum, lambda: False)
        return func()

    def recetangle(self,p1,p2,p3,p4,p):
        if self.insideline(p1,p2,p)>=0 and self.insideline(p2,p3,p)>=0 and self.insideline(p3,p4,p)>=0 and self.insideline(p4,p1,p)>=0:
            return True

    def insideline(self,p1,p2,p):
        A = -(p2[1] - p1[1])
        B = p2[0] - p1[0]
        C = -(A * p1[0] + B * p1[1])
        return  A * p[0] + B * p[1] + C

    def none(self):
        return False

    def one(self):

       x=self.markers[0].id
       if x==1244:
           return self.recetangle(self.markers[0].center,(self.screenwidth,self.markers[0].center[1]),(self.screenwidth,self.screenheight),(self.markers[0].center[0],self.screenheight),(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
       elif x==2215:
           return self.recetangle((0,self.markers[0].center[1]),self.markers[0].center,(self.markers[0].center[0],self.screenheight),(0,self.screenheight),(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
       elif x==2266:
           return self.recetangle((self.markers[0].center[0],0),(self.screenwidth,0),(self.screenwidth,self.markers[0].center[1]),self.markers[0].center,(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
       elif x==3632:
           return self.recetangle((0,0),(self.markers[0].center[0],0),self.markers[0].center,(0,self.markers[0].center[1]),(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
       else: return False


    def two(self):
       markers_1244 = [x for x in self.markers if x.id == 1244]
       markers_2215 = [x for x in self.markers if x.id == 2215]
       markers_2266 = [x for x in self.markers if x.id == 2266]
       markers_3632 = [x for x in self.markers if x.id == 3632]
       x=self.markers[0].id+self.markers[1].id

       if x==3459:
           return self.recetangle(markers_1244[0].center,markers_2215[0].center,(markers_2215[0].center[0],self.screenheight),(markers_1244[0].center[0],self.screenheight),(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
       elif x==5847:
           return self.recetangle((0,markers_2215[0].center[1]),markers_2215[0].center,markers_3632[0].center,(0,markers_3632[0].center[1]),(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
       elif x==5898:
           return self.recetangle((markers_2266[0].center[0],0),(markers_3632[0].center[0],0),markers_3632[0].center,markers_2266[0].center,(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
       elif x==3510:
           return self.recetangle(markers_1244[0].center,(self.screenwidth,markers_1244[0].center[1]),(self.screenwidth,markers_2266[0].center[1]),markers_2266[0].center,(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
       else: return False

    def three(self):
       markers_1244 = [x for x in self.markers if x.id == 1244]
       markers_2215 = [x for x in self.markers if x.id == 2215]
       markers_2266 = [x for x in self.markers if x.id == 2266]
       markers_3632 = [x for x in self.markers if x.id == 3632]
       x=self.markers[0].id+self.markers[1].id+self.markers[2].id
       if x==7091:
           return self.recetangle(markers_1244[0].center,markers_2215[0].center,markers_3632[0].center,self.forthpoint(markers_1244[0].center,markers_2215[0].center,markers_3632[0].center),(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
       elif x==5725:
           return self.recetangle(markers_1244[0].center,markers_2215[0].center,self.forthpoint(markers_2215[0].center,markers_1244[0].center,markers_2266[0].center),markers_2266[0].center,(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
       elif x==8113:
           return self.recetangle(self.forthpoint(markers_2215[0].center,markers_3632[0].center,markers_2266[0].center),markers_2215[0].center,markers_3632[0].center,markers_2266[0].center,(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
       elif x==7142:
           return self.recetangle(markers_1244[0].center,self.forthpoint(markers_1244[0].center,markers_2266[0].center,markers_3632[0].center),markers_3632[0].center,markers_2266[0].center,(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
       else: return False

    def four(self):
       markers_1244 = [x for x in self.markers if x.id == 1244]
       markers_2215 = [x for x in self.markers if x.id == 2215]
       markers_2266 = [x for x in self.markers if x.id == 2266]
       markers_3632 = [x for x in self.markers if x.id == 3632]
       return  self.recetangle(markers_1244[0].center,markers_2215[0].center,markers_3632[0].center,markers_2266[0].center,(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight))),

    def forthpoint(self,p1,p2,p3):
        return (p1[0]+p3[0]-p2[0],p1[1]+p3[1]-p2[1])
	# }



    #  Main UI: show video frame with gaze point in loop 
    def show_frame(self):
        global job
        self.videoframe.grid(row=0, column=0)
        #self.canvas.delete("all")
        if self.capture.isOpened(): # try to get the first frame
           frame_captured,frame = self.capture.read()
        else:
           frame_captured = False
        img2=cv2.resize(frame,(int(self.screenwidth),int(self.screenheight)))
        self.markers = detect_markers(img2)


        # condition show screen (4 markers)
        # from xpos,ypos from data
        if self.markers.__len__()>1:
            self.parent.wm_title(self.str+" markers num: "+str(self.markers.__len__()))
        else:
            self.parent.wm_title(self.str+" markers num: "+str(self.markers.__len__())+" Please detect more than 1 markers")
        self.point=self.gazescreen(self.markers.__len__())

        self.usedx=self.point[0]/(self.screenwidth*2)
        self.usedy=self.point[1]/((self.screenheight*2)-int(88*(self.screenheight*2/768)))
        self.textovl.set_property("xpos",self.usedx)
        self.textovl.set_property("ypos",self.usedy)
        self.outputfile=open(self.filepath,'a')
        self.outputfile.write('{ "x" : "'+str(self.usedx)+'" , "y" : "'+str(self.usedy)+'" , "ts" : "'+str(time.time()-self.starttime)+'" }\n')
		# Write gaze data into document
		
        job=self.videoframe.after(1, self.show_frame)
		
    # "Where is gaze on screen" algorithm
	# {
    def gazescreen(self,marknum):
        switcher={
            0: self.gazeone_none,
            1: self.gazeone,
            2: self.gazetwo,
            3: self.gazetwo,
            4: self.gazetwo,
        }
        func = switcher.get(marknum, lambda:(0,0))
        return func()


    def gazeone_none(self):

        return (0,0)

    def gazeone(self):
        pointxy=self.point
        return pointxy

    def gazetwo(self):
        markers_1244 = [x for x in self.markers if x.id == 1244]
        markers_2215 = [x for x in self.markers if x.id == 2215]
        markers_2266 = [x for x in self.markers if x.id == 2266]
        markers_3632 = [x for x in self.markers if x.id == 3632]

        x=self.markers[0].id+self.markers[1].id

        if x==3459:
           return self.gaze_3459(markers_1244[0].center,markers_2215[0].center,(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
        elif x==5847:
           return self.gaze_5847(markers_2215[0].center,markers_3632[0].center,(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
        elif x==5898:
           return self.gaze_5898(markers_3632[0].center,markers_2266[0].center,(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
        elif x==3510:
           return self.gaze_3510(markers_2266[0].center,markers_1244[0].center,(int(gazepoint[0]*self.screenwidth),int(gazepoint[1]*self.screenheight)))
        else: return (0,0)

    def gaze_3459(self,p1,p2,p):
        gY=self.point3area(p1,p2,p)/self.pointtopoint(p1,p2)*self.percentagewidth(p1,p2)
        gX=math.sqrt(1.0-math.pow((self.point3area(p1,p2,p)/self.pointtopoint(p1,p2)/self.pointtopoint(p,p1)),2))*self.pointtopoint(p,p1)*self.percentagewidth(p1,p2)
        return (gX+self.changeX,gY+self.changeY)

    def gaze_5847(self,p1,p2,p):
        gX=self.screenwidth*2-self.point3area(p1,p2,p)/self.pointtopoint(p1,p2)*self.percentagehight(p1,p2)
        gY=math.sqrt(1.0-math.pow((self.point3area(p1,p2,p)/self.pointtopoint(p1,p2)/self.pointtopoint(p,p1)),2))*self.pointtopoint(p,p1)*self.percentagehight(p1,p2)
        return (gX+self.changeX,gY+self.changeY)

    def gaze_5898(self,p1,p2,p):
        gY=self.screenheight*2-self.point3area(p1,p2,p)/self.pointtopoint(p1,p2)*self.percentagewidth(p1,p2)
        gX=math.sqrt(1.0-math.pow((self.point3area(p1,p2,p)/self.pointtopoint(p1,p2)/self.pointtopoint(p,p2)),2))*self.pointtopoint(p,p2)*self.percentagewidth(p1,p2)
        return (gX+self.changeX,gY+self.changeY)

    def gaze_3510(self,p1,p2,p):
        gX=self.point3area(p1,p2,p)/self.pointtopoint(p1,p2)*self.percentagehight(p1,p2)
        gY=math.sqrt(1.0-math.pow((self.point3area(p1,p2,p)/self.pointtopoint(p1,p2)/self.pointtopoint(p,p2)),2))*self.pointtopoint(p,p2)*self.percentagehight(p1,p2)
        return (gX+self.changeX,gY+self.changeY)

    def percentagewidth(self,p1,p2):
        return self.screenwidth*2/self.pointtopoint(p1,p2)

    def percentagehight(self,p1,p2):
        return self.screenheight*2/self.pointtopoint(p1,p2)
    def point3area(self,p1,p2,p3):
        x1=p1[0]
        y1=p1[1]
        x2=p2[0]
        y2=p2[1]
        x3=p3[0]
        y3=p3[1]
        return x1*y2*1.0+x2*y3*1.0+x3*y1*1.0-x1*y3*1.0-x2*y1*1.0-x3*y2*1.0

    def pointtopoint(self,p1,p2):
        x1=p1[0]
        y1=p1[1]
        x2=p2[0]
        y2=p2[1]
        return math.sqrt(math.pow((x1*1.0-x2),2)+math.pow((y1*1.0-y2),2))
	# }






    def display_as_cvwindow(self):
        #self.lmain.after_cancel(job)
        self.capture.release()
        self.capture = cv2.VideoCapture("123.sdp")
        #self.show_frame()



# Main Loop Set up
def video():
    gobject.threads_init()
    root = Tk()
    app = Prototype(root)
    app.pack(expand="yes", fill="both")
    def refreshApp():
        app.update()
        return True

    gobject.idle_add(refreshApp)
    ml = gobject.MainLoop()


    # Enter main loop
    ml.run()

if __name__ == '__main__':
    video()





        
        
