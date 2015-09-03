using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using System.Runtime.InteropServices;
using Solution.Data;

namespace Solution.View
{
    class VideoModel
    {

        // Define the state enum
        enum State {
            Uninit,
            Stopped,
            Paused,
            Playing
        }

        // Put the private class variables
        private State m_State = State.Uninit;
        private DxPlay m_play = null;
        public String Filename; 

        // Constructor
        public VideoModel() {
        }

        // Destructor
        ~VideoModel() {
            if(m_play != null) {
                m_play.Dispose();
            }
        }

        // Loads a video. Returns true on success and false on error
        public Boolean loadVideo(String fileName, Panel panel) 
        {
            // If necessary, close the old file
            if (m_State == State.Stopped || m_State == State.Paused) 
            {
                // Did the filename change?
                if (fileName != m_play.FileName) 
                {
                    if (m_State == State.Paused)
                    {
                        m_play.Stop();
                    }
                    // File name changed, close the old file
                    m_play.Dispose();
                    m_play = null;
                    m_State = State.Uninit;
                }
            }

            // If we have no file open
            if (m_play == null) 
            {
                try 
                {
                    this.Filename = fileName;

                    // Open the file, provide a handle to play it in
                    m_play = new DxPlay(panel, fileName);

                    // Let us know when the file is finished playing
                    m_play.StopPlay += new DxPlay.DxPlayEvent(m_play_StopPlay);
                    m_State = State.Stopped;

                    return true;
                }
                catch (COMException ce)
                {
                    MessageBox.Show("Failed to open file: " + ce.Message, "Open Error", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    return false;
                }
            }

            return true;
        }

        // Play a video
        public void playVideo()
        {
            if (m_play != null)
            {
                if (m_State == State.Stopped || m_State == State.Paused)
                {
                    m_play.Start();
                    m_State = State.Playing;
                }
            }
        }


        // Play a shot
        public void playShot(Shot shot)
        {
            if (m_play != null)
            {
                m_play.PlayShot(shot.StartFrame, shot.EndFrame);
                    
                if (m_State == State.Stopped || m_State == State.Paused)
                {
                    m_play.Start();
                    m_State = State.Playing;
                }
             }
        }

        // Pause a video
        public void pauseVideo()
        {
            // If we are playing, pause
            if (m_State == State.Playing)
            {
                m_play.Pause();
                m_State = State.Paused;
            }
        }

        // Stop the video
        public void stopVideo()
        {
            // If we are playing or paused: stop the video, and move it to the beginning
            if (m_State == State.Playing || m_State == State.Paused)
            {
                m_play.Stop();
                m_State = State.Stopped;
                m_play.Rewind();
            }
        }

        // Rewind the video
        public void rewindVideo()
        {
            m_play.Rewind();
        }

        // Called when the video is finished playing
        private void m_play_StopPlay(Object sender)
        {
            m_State = State.Stopped;

            m_play.Rewind();
        }
    }
}
