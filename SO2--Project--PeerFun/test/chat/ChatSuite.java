/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package chat;

import junit.framework.Assert;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import userManagement.Friend;
import userManagement.User;

/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
public class ChatSuite {

	static User user;

	@BeforeClass
	public static void setUpClass() throws Exception {
		user = new User("Test", "Tester", "Testerdetest", null, 0);
		Chat.getSingleton().getChatTabbedModel().setUser(user);
	}

	@AfterClass
	public static void tearDownClass() throws Exception {
	}

	@Test
	public void addChats() { // Hier komt test code }		
		Chat.getSingleton().addChat("Chat1");
		Assert.assertNotNull(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat1"));

		Chat.getSingleton().addChat("Chat2");
		Assert.assertNotNull(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat2"));
	}

	@Test
	public void removeChats() { // Hier komt test code }
		Chat.getSingleton().addChat("Chat3");
		Assert.assertNotNull(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat1"));

		Chat.getSingleton().addChat("Chat4");
		Assert.assertNotNull(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat2"));

		Chat.getSingleton().removeChat("Chat3");
		Assert.assertNull(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat3"));
	}

	@Test
	public void addChatters() {
		Chat.getSingleton().addChat("Chat1");
		Chat.getSingleton().addChatter("Chat1", new Friend("Tester1", "Testerken1", null));
		Chat.getSingleton().addChatter("Chat1", new Friend("Tester2", "Testerken2", null));

		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat1").getModel().getChatters().size(), 3);
	}

	@Test
	public void removeChatters() {
		Friend friend1 = new Friend("Tester1", "Testerken1", null);
		Friend friend2 = new Friend("Tester2", "Testerken2", null);

		Chat.getSingleton().addChat("Chat2");
		
		Chat.getSingleton().addChatter("Chat2", friend1);
		Chat.getSingleton().addChatter("Chat2", friend2);

		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat2").getModel().getChatters().size(), 3);

		
		Chat.getSingleton().removeChatter("Chat2", friend2);
		
		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat2").getModel().getChatters().size(), 2);
	}
	
	@Test
	public void addChattersToDifferentRooms() {
		Friend friend1 = new Friend("Tester1", "Testerken1", null);
		Friend friend2 = new Friend("Tester2", "Testerken2", null);

		Chat.getSingleton().addChat("Chat7");
		Chat.getSingleton().addChat("Chat8");
		
		Chat.getSingleton().addChatter("Chat7", friend1);
		Chat.getSingleton().addChatter("Chat8", friend2);

		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat7").getModel().getChatters().size(), 2);		
		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat8").getModel().getChatters().size(), 2);
	}	
	
	@Test
	public void addAndRemoveChattersToDifferentRooms() {
		Friend friend1 = new Friend("Tester1", "Testerken1", null);
		Friend friend2 = new Friend("Tester2", "Testerken2", null);

		Chat.getSingleton().addChat("Chat9");
		Chat.getSingleton().addChat("Chat10");
		
		Chat.getSingleton().addChatter("Chat9", friend1);
		Chat.getSingleton().addChatter("Chat10", friend2);

		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat9").getModel().getChatters().size(), 2);		
		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat10").getModel().getChatters().size(), 2);
		
		Chat.getSingleton().removeChatter("Chat9", friend1);
		Chat.getSingleton().removeChatter("Chat10", friend2);

		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat9").getModel().getChatters().size(), 1);		
		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat10").getModel().getChatters().size(), 1);
	}
	
	@Test
	public void sendTextToChat() {
		Chat.getSingleton().addChat("Chat1");
		Chat.getSingleton().addChatMessage("Chat1", user.getAlias(), "Een chatbericht!");
		
		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat1").getModel().getFrom(), user.getAlias());
		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat1").getModel().getText(), "Een chatbericht!");
	}
	
	@Test
	public void sendTextToDifferentChatWindows() {
		Chat.getSingleton().addChat("Chat1");
		Chat.getSingleton().addChatMessage("Chat1", user.getAlias(), "Een chatbericht!");
		
		Chat.getSingleton().addChat("Chat2");
		Chat.getSingleton().addChatMessage("Chat2", user.getAlias(), "Een ander chatbericht!");
		
		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat1").getModel().getText(), "Een chatbericht!");
		Assert.assertNotSame(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat1").getModel().getText(), "Een ander chatbericht!");
		
		Assert.assertEquals(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat2").getModel().getText(), "Een ander chatbericht!");
		Assert.assertNotSame(Chat.getSingleton().getChatTabbedModel().getTeamIdChatMap().get("Chat2").getModel().getText(), "Een chatbericht!");
	}
}
