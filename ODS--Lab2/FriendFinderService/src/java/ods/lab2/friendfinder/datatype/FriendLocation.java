/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ods.lab2.friendfinder.datatype;

import java.io.Serializable;

/**
 * This datatype is a Serializable implementation of the combined information
 * between the unique identifier and the location of that person. It has three 
 * variables, the serializable FriendID version for the unique identifier, a 
 * double for the longitude and a double for the latitude.
 *
 * @author fdebacke
 */
public class FriendLocation implements Serializable {
    
    private FriendID friendID = null;
    private double longitude;
    private double latitude;
    
    public FriendLocation(FriendID friendID, double longitude, double latitude) {
        this.friendID = friendID;
        this.longitude = longitude;
        this.latitude = latitude;
    }
    
    public FriendLocation() {
    }

    public FriendID getFriendID() {
        return friendID;
    }

    public void setFriendID(FriendID friendID) {
        this.friendID = friendID;
    }

    public double getLatitude() {
        return latitude;
    }

    public void setLatitude(double latitude) {
        this.latitude = latitude;
    }

    public double getLongitude() {
        return longitude;
    }

    public void setLongitude(double longitude) {
        this.longitude = longitude;
    }

    @Override
    public String toString() {
        return friendID.getId() + ": " + this.getLongitude() + " - " + this.getLatitude();
    }
    
    

}
