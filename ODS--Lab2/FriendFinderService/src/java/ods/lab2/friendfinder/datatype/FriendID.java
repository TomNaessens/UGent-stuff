/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ods.lab2.friendfinder.datatype;

import java.io.Serializable;

/**
 * This datatype represents the Serializable version of the FriendID unique
 * identifier of the DBWrapper.
 * 
 * @author fdebacke
 */
public class FriendID implements Serializable {
    
    private int id;
    private long checksum;
    private String name;
    
    public FriendID(int id, long checksum, String name) {
        this.id = id;
        this.checksum = checksum;
        this.name = name;
    }
    
    public FriendID() {
        
    }

    public long getChecksum() {
        return checksum;
    }

    public void setChecksum(long checksum) {
        this.checksum = checksum;
    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return id + " - " + checksum + " - " + name;
    }

}
