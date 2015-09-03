/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ods.lab2.friendfinder.datatype;

import java.io.Serializable;

/**
 * Serializable Wrapper class around an array containing a number of
 * FriendLocation objects. Its purpose is to represent a list of persons 
 * without each other's neighbourhood
 * 
 * @author fdebacke
 */
public class FriendLocationList implements Serializable {
    
    private FriendLocation[] friendLocations = null;
    
    public FriendLocationList() {
        friendLocations = new FriendLocation[0];
    }

    public FriendLocation[] getFriendLocations() {
        return friendLocations;
    }

    public void setFriendLocations(FriendLocation[] friendLocations) {
        this.friendLocations = friendLocations;
    }
    
    public void addFriendLocation(FriendLocation friendLocation) {
        FriendLocation[] newFriendLocations = new FriendLocation[friendLocations.length+1];
        for (int i = 0; i < friendLocations.length; i++) {
            newFriendLocations[i] = friendLocations[i];
        }
        newFriendLocations[newFriendLocations.length-1] = friendLocation;
        friendLocations = newFriendLocations;
    }

    @Override
    public String toString() {
        String returnString = "-----------\n";
        for (int i = 0; i < this.friendLocations.length; i++) {
            returnString += friendLocations[i].toString() + "\n";
        }
        returnString += "-------------------\n";
        return returnString;
    }
    
    
}
