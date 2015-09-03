package userManagement;

import java.io.Serializable;
import java.net.InetAddress;

/**
 * @author NVH @filename Friend.java
 */
public class Friend implements Serializable {

	private String name;
	private InetAddress ip;
	private FriendStatus status;
	private String alias;

	public Friend(String name, String alias, InetAddress ip) {
		this.name = name;
		this.ip = ip;
		this.alias = alias;
		this.status = FriendStatus.OFFLINE;
	}

	public InetAddress getIp() {
		return ip;
	}

	public void setIp(InetAddress ip) {
		this.ip = ip;
	}
	
	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public FriendStatus getStatus() {
		return status;
	}

	public void setStatus(FriendStatus status) {
		this.status = status;
	}

	public String getAlias() {
		return alias;
	}

	public void setAlias(String alias) {
		this.alias = alias;
	}
	
	@Override
	public String toString() {
		return "Name: " + name + "\tIP: " + ip.getHostAddress();
	}
}
