/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ods.lab2.friendfinder.service;

import java.util.Iterator;
import java.util.Map;
import ods.lab2.friendfinder.datatype.FriendLocation;
import ods.lab2.friendfinder.datatype.FriendLocationList;
import ods.lab2.friendfinder.datatype.Point;
import ods.lab2.friendfinder.datatype.Vector;
import ods.lab2.friendfinderdbwrapper.DBWrapper;
import ods.lab2.friendfinderdbwrapper.datatype.LocationCoordinates;

/**
 *
 * @author fdebacke
 */
public class FriendFinderService {
    
    private DBWrapper dbWrapper = null;
    
    /**
     * This Web Method adds a new friend into the database, and connects it to a
     * certain group. Please use your labsession group number, as the reference
     * to the group. This method also returns a unique friend identifier object.
     * This UID is to be cached and reused in case of location updates and deletion
     * of friends from the database.
     */
    
    //TODO: Implement addFriend method!

    /**
     * This Web Method updates the location of a specific person. It takes the
     * unique identifier as argument. 
     */   
    
    //TODO: Implement updateFriendLocation method!
    
    /**
     * This Web Method deletes a person from the database. The unique identifier
     * is to be provided as an argument. 
     */    
    
    //TODO: Implement deleteFriend method!
    
     /**
     * This Web Method returns a Wrapper instance of the FriendLocationList.
     * It contains the FriendLocation objects of all persons in the group number
     * given as an argument, within a certain range given as an argument, of
     * a person referred to with the unique identifier given as the third
     * argument.
     * 
     * @param groupID int: Identifier of the group. Please use you labsession
     * group number for this.
     * @param personID FriendID: Unique identifier of the person which was returned
     * when adding this person to the application.
     * @param distance double: The length of half a side of the square to be
     * considered as the range around the person.
     * @return FriendLocationList: Serializable wrapper containing an array of
     * FriendLocation objects, referring to the location and the unique identifier
     * of the friends within a certain range
     */
    public ods.lab2.friendfinder.datatype.FriendLocationList getGroupFriendLocations(
            int groupID, ods.lab2.friendfinder.datatype.FriendID personID, double distance) {
        dbWrapper = new DBWrapper();
        Map<ods.lab2.friendfinderdbwrapper.datatype.FriendID, ods.lab2.friendfinderdbwrapper.datatype.LocationCoordinates> friendLocations = dbWrapper.getFriendLocations(groupID);

        FriendLocationList friendLocationList = new FriendLocationList();
        Iterator<ods.lab2.friendfinderdbwrapper.datatype.FriendID> it = friendLocations.keySet().iterator();
        ods.lab2.friendfinderdbwrapper.datatype.FriendID friendID = null;
        while (it.hasNext()) {
            friendID = it.next();
            Point p =new Point(friendLocations.get(friendID).getLongitude(),friendLocations.get(friendID).getLatitude());
            LocationCoordinates personCoordinates = dbWrapper.getFriendIDLocationCoordinates(
                    new ods.lab2.friendfinderdbwrapper.datatype.FriendID(personID.getId(), personID.getChecksum(), personID.getName()));
            LocationCoordinates[] polygonCoordinates = new LocationCoordinates[4];
            polygonCoordinates[0] = new LocationCoordinates(personCoordinates.getLongitude()-distance, personCoordinates.getLatitude()-distance);
            polygonCoordinates[1] = new LocationCoordinates(personCoordinates.getLongitude()+distance, personCoordinates.getLatitude()-distance);
            polygonCoordinates[2] = new LocationCoordinates(personCoordinates.getLongitude()+distance, personCoordinates.getLatitude()+distance);
            polygonCoordinates[3] = new LocationCoordinates(personCoordinates.getLongitude()-distance, personCoordinates.getLatitude()+distance);
            if(pointInRectangle(polygonCoordinates,p)){
                friendLocationList.addFriendLocation(new FriendLocation(new ods.lab2.friendfinder.datatype.FriendID(friendID.getId(), friendID.getChecksum(), friendID.getName()), p.getX(), p.getY()));
            }
        }
        return friendLocationList;
    }
    
     /**
     * Checks if a certain point is within the boundaries of 
     * a rectangle, defined through an array of coordinates, 
     * 
     * @param polygonCoordinates the coordinates of the array
     * @param x
     * @return
     */
    private boolean pointInRectangle(LocationCoordinates[] polygonCoordinates,Point x){
    	if(polygonCoordinates.length!=4)
    		throw new IllegalArgumentException("The coordinates should form a rectangle");
    	
    	Point c = new Point(polygonCoordinates[1].getLongitude(),polygonCoordinates[1].getLatitude());
    	Point c1 = new Point(polygonCoordinates[2].getLongitude(),polygonCoordinates[2].getLatitude());
    	Point c2 = new Point(polygonCoordinates[0].getLongitude(),polygonCoordinates[0].getLatitude());

    	//Create a vector based on the rectangle
    	Vector v1 = new Vector(c,c1);    	
    	Vector v2 = new Vector(c,c2);
    	Vector v = new Vector(c,x);

    	return 0<=v.dotProduct(v1) && v.dotProduct(v1)<=v1.dotProduct(v1) 
    	&& 0<= v.dotProduct(v2) && v.dotProduct(v2) <= v2.dotProduct(v2);
    }
}
