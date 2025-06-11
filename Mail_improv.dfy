/*===============================================
  M.EIC037: Formal Methods For Critical Systems

  Project 2 

  Your name(s):
  Pedro
  Bruno
  José 
  ===============================================*/





// ===============================================
// ===============================================
// INITIAL IS_READ(ITS ALL WRONG)
// ===============================================
// ===============================================
include "List.dfy"

import opened L = List

// The next three classes have a minimal class definition,
// for simplicity
class Address {
  var value: string


  constructor(v: string)
    requires v != ""
    ensures value == v
  {
    value := v;
  }
}


class Date {
  var timestamp: int

  constructor(t: int)
    ensures timestamp == t
  {
    timestamp := t;
  }
}


class MessageId {
  var id: int

  constructor(i: int)
    ensures id == i
  {
    id := i;
  }
}


//==========================================================
//  Message
//==========================================================
class Message
  {
  var id: MessageId
  var content: string
  var date: Date
  var sender: Address
  var recipients: L.List<Address>
  var isRead: bool  // New field to track read status

  constructor(s: Address)
    ensures fresh(id)
    ensures fresh(date)
    ensures content == ""
    ensures sender == s
    ensures recipients == L.Nil
    ensures !isRead     // Messages are unread by default
  {
    id := new MessageId(0);  // placeholder
    date := new Date(0);     // placeholder
    content := "";
    sender := s;
    recipients := L.Nil;
    isRead := false;
  }

  method setContent(c: string)
    modifies this
    ensures content == c
    ensures {id, date, sender} == old({id, date, sender})
    ensures recipients == old(recipients)
    ensures isRead == old(isRead)  // Preserve read status
  {
    content := c;
  }

  method setDate(d: Date)
    modifies this
    ensures date == d
    ensures {id, sender} == old({id, sender})
    ensures recipients == old(recipients)
    ensures content == old(content)
    ensures isRead == old(isRead)  // Preserve read status
  {
    date := d;
  }

  method addRecipient(position: nat, recipient: Address)
    modifies this
    requires position <= L.len(recipients) // allow adding at the end
    ensures L.len(recipients) == L.len(old(recipients)) + 1
    ensures L.elementSeq(recipients) ==
            L.elementSeq(L.take(old(recipients), position)) + [recipient] + L.elementSeq(L.drop(old(recipients), position))
    ensures {id, date, sender} == old({id, date, sender})
    ensures content == old(content)
    ensures isRead == old(isRead)  // Preserve read status
  {
    recipients := InsertAt(recipients, position, recipient);
  }

  // Marks the message as read
  method markAsRead()
    modifies this
    ensures isRead
    ensures id == old(id)
    ensures content == old(content)
    ensures date == old(date)
    ensures sender == old(sender)
    ensures recipients == old(recipients)
  {
    isRead := true;
  }

  // Marks the message as unread
  method markAsUnread()
    modifies this
    ensures !isRead
    ensures id == old(id)
    ensures content == old(content)
    ensures date == old(date)
    ensures sender == old(sender)
    ensures recipients == old(recipients)
  {
    isRead := false;
  }
}

// Helper function to insert an element at a given position in a List
function InsertAt<T>(l: L.List<T>, p: nat, x: T): L.List<T>
  requires p <= L.len(l)
  ensures L.len(InsertAt(l, p, x)) == L.len(l) + 1
  ensures L.elementSeq(InsertAt(l, p, x)) ==
          L.elementSeq(L.take(l, p)) + [x] + L.elementSeq(L.drop(l, p))
{
  if p == 0 then
    Cons(x, l)
  else
    match l
    case Cons(h, t) => Cons(h, InsertAt(t, p - 1, x))
    case Nil => Nil // unreachable due to requires
}





//==========================================================
//  Mailbox
//==========================================================
//
// Each Mailbox has a name, which is a string.
// Its main content is a set of messages.
//
class Mailbox {
  var name: string
  var messages: set<Message>

  // Creates an empty mailbox with name n
  constructor(n: string)
    requires n != "" // <- Enforced here
    ensures name == n
    ensures messages == {} // <- Empty on creation
  {
    name := n;
    messages := {};
  }

  // Adds message m to the mailbox
  method add(m: Message)
    modifies this
    ensures messages == old(messages) + {m}
    ensures name == old(name)
  {
    messages := messages + {m};
  }

  // Removes message m from mailbox
  // m need not be in the mailbox
  method remove(m: Message)
    modifies this
    ensures messages == old(messages) - {m}
    ensures name == old(name)
  {
    messages := messages - { m };
  }

  // Empties the mailbox
  method empty()
    modifies this
    ensures messages == {}
    ensures name == old(name)
  {
    messages := {};
  }

  // Returns the count of unread messages in the mailbox
  method countUnread() returns (count: nat)
    ensures count == |set m | m in messages && !m.isRead|
  {
    count := 0;
    var unreadMessages := set m | m in messages && !m.isRead;
    count := |unreadMessages|;
  }

  // Marks all messages in the mailbox as read
  method markAllAsRead()
    modifies this, messages
    ensures forall m :: m in messages ==> m.isRead
    ensures messages == old(messages)
    ensures name == old(name)
  {
    var msgs := messages;
    while msgs != {}
      decreases |msgs|
      modifies msgs
      invariant msgs <= messages
      invariant forall m :: m in messages && m !in msgs ==> m.isRead
    {
      var m :| m in msgs;
      m.markAsRead();
      msgs := msgs - {m};
    }
  }
}

ghost function ListElements<T>(l: L.List<T>): set<T>
{
  match l
  case Nil => {}
  case Cons(h, t) => {h} + ListElements(t)
}

lemma RemovePreservesExclusion<T(==)>(l: List<T>, x: T, y: T)
  ensures y !in elements(l) ==> y !in elements(L.remove(l, x))
{
  match l
  case Nil => {}
  case Cons(h, t) =>
    if x == h {
      RemovePreservesExclusion(t, x, y);
    } else {
      RemovePreservesExclusion(t, x, y);
    }
}

// This lemma is used to prove that the system boxes
// are not in the userBoxes after a mailbox is removed
// from the userBoxes. It is used in the deleteMailbox
// method of the MailApp class.
lemma RemovePreservesSystemBoxes(l: List<Mailbox>, x: Mailbox, i: Mailbox, d: Mailbox, t: Mailbox, s: Mailbox)
  requires i !in ListElements(l)
  requires d !in ListElements(l)
  requires t !in ListElements(l)
  requires s !in ListElements(l)
  ensures i !in ListElements(remove(l, x))
  ensures d !in ListElements(remove(l, x))
  ensures t !in ListElements(remove(l, x))
  ensures s !in ListElements(remove(l, x))
{
  RemovePreservesExclusion(l, x, i);
  RemovePreservesExclusion(l, x, d);
  RemovePreservesExclusion(l, x, t);
  RemovePreservesExclusion(l, x, s);
}


//==========================================================
//  MailApp
//==========================================================


class MailApp {
  // abstract field for user defined boxes
  ghost var userBoxes: set<Mailbox>

  // abstract function returning all system mailboxes in one set
  ghost function systemBoxes(): set<Mailbox>
    reads this
  { {inbox, drafts, trash, sent} }

  // the inbox, drafts, trash and sent are both abstract and concrete
  var inbox: Mailbox
  var drafts: Mailbox
  var trash: Mailbox
  var sent: Mailbox

  // userboxList implements userBoxes
  var userboxList: List<Mailbox>

  // Class invariant
  ghost predicate isValid() reads this {
    // Abstract state invariants
    // 1. all system mailboxes (inbox, ..., sent) are distinct
    inbox != drafts &&
    inbox != sent &&
    inbox != trash &&
    drafts != sent &&
    drafts != trash &&
    sent != trash &&
    // 2. none of the system mailboxes are in the set
    //    of user-defined mailboxes
    inbox !in userBoxes &&
    drafts !in userBoxes &&
    trash !in userBoxes &&
    sent !in userBoxes &&
    // Abstract-to-concrete state invariants
    // userBoxes is the set of mailboxes in userboxList
    userBoxes == ListElements(userboxList)
  }

  constructor ()
    ensures inbox.name == "Inbox" && fresh(inbox)
    ensures drafts.name == "Drafts" && fresh(drafts)
    ensures trash.name == "Trash" && fresh(trash)
    ensures sent.name == "Sent" && fresh(sent)
    ensures inbox.messages == {}
    ensures drafts.messages == {}
    ensures trash.messages == {}
    ensures sent.messages == {}
    ensures userBoxes == {}
    ensures isValid()
  {
    inbox := new Mailbox("Inbox");
    drafts := new Mailbox("Drafts");
    trash := new Mailbox("Trash");
    sent := new Mailbox("Sent");
    userBoxes := {};
    userboxList := Nil;
  }

  // Deletes user-defined mailbox mb
  method deleteMailbox(mb: Mailbox)
    modifies this, mb
    requires isValid()
    requires mb in userBoxes
    ensures isValid()
  {
    // Prove that system boxes stay out of the updated userBoxes
    RemovePreservesSystemBoxes(userboxList, mb, inbox, drafts, trash, sent);

    userboxList := remove(userboxList, mb);
    userBoxes := ListElements(userboxList);
    mb.empty();
  }

  // Adds a new mailbox with name n to set of user-defined mailboxes
  // provided that no user-defined mailbox has name n already
  method newMailbox(n: string)
    modifies this
    requires isValid()
    requires n != ""
    requires forall mb: Mailbox :: mb in userBoxes ==> mb.name != n
    ensures isValid()
    ensures exists mb: Mailbox :: mb in userBoxes && mb.name == n && mb.messages == {}
    ensures drafts == old(drafts)
    ensures fresh(userBoxes - old(userBoxes))
  {
    var mb := new Mailbox(n);
    userboxList := Cons(mb, userboxList);
    userBoxes := ListElements(userboxList);
  }

  // Adds a new message with sender s to the drafts mailbox
  method newMessage(s: Address)
    modifies this, drafts
    requires isValid()
    ensures isValid()
    ensures exists m: Message :: m in drafts.messages && m.sender == s && fresh(m)
    ensures |drafts.messages| == |old(drafts.messages)| + 1
    ensures forall m: Message :: m in old(drafts.messages) ==> m in drafts.messages
    ensures old(drafts.messages) == {} ==> (exists m: Message :: drafts.messages == {m})
  {
    var m := new Message(s);
    drafts.add(m);
  }

  // Moves message m from mailbox mb1 to a different mailbox mb2
  method moveMessage(m: Message, fromMailbox: Mailbox, toMailbox: Mailbox)
    modifies this, fromMailbox, toMailbox
    requires isValid()
    requires fromMailbox != toMailbox
    ensures isValid()
    ensures m !in fromMailbox.messages
    ensures m in toMailbox.messages
    ensures fromMailbox.messages == old(fromMailbox.messages) - {m}
    ensures toMailbox.messages == old(toMailbox.messages) + {m}
  {
    fromMailbox.remove(m);
    toMailbox.add(m);
  }

  // Moves message m from non-null mailbox mb to the trash mailbox
  // provided that mb is not the trash mailbox
  method deleteMessage(m: Message, mb: Mailbox)
    modifies this, mb, trash
    requires isValid()
    requires mb != trash
    ensures isValid()
  {
    moveMessage(m, mb, trash);
  }

  // Moves message m from the drafts mailbox to the sent mailbox
  method sendMessage(m: Message)
    modifies this, drafts, sent
    requires isValid()
    ensures isValid()
  {
    moveMessage(m, drafts, sent);
  }

  // Empties the trash mailbox
  method emptyTrash()
    modifies this, trash
    requires isValid()
    ensures isValid()
  {
    trash.empty();
  }

  // Returns the total number of unread messages across all mailboxes
  method totalUnreadMessages() returns (count: nat)
    requires isValid()
    ensures count == |set m | m in inbox.messages && !m.isRead| + 
                    |set m | m in drafts.messages && !m.isRead| +
                    |set m | m in sent.messages && !m.isRead| +
                    |set m | m in trash.messages && !m.isRead| +
                    |set mb, m | mb in userBoxes && m in mb.messages && !m.isRead|
  {
    var inboxUnread := inbox.countUnread();
    var draftsUnread := drafts.countUnread();
    var sentUnread := sent.countUnread();
    var trashUnread := trash.countUnread();
    
    count := inboxUnread + draftsUnread + sentUnread + trashUnread;
    
    // Count unread messages in user mailboxes
    var remaining := userboxList;
    while remaining != Nil
      decreases |remaining|
      invariant count == |set m | m in inbox.messages && !m.isRead| + 
                         |set m | m in drafts.messages && !m.isRead| +
                         |set m | m in sent.messages && !m.isRead| +
                         |set m | m in trash.messages && !m.isRead| +
                         |set mb, m | mb in (ListElements(userboxList) - ListElements(remaining)) && m in mb.messages && !m.isRead|
    {
      match remaining {
        case Cons(mb, rest) => 
          var mbUnread := mb.countUnread();
          count := count + mbUnread;
          remaining := rest;
      }
    }
  }

  // Mark a message as read
  method readMessage(m: Message)
    modifies m
    requires isValid()
    requires m in inbox.messages || m in sent.messages || m in drafts.messages || m in trash.messages || 
             (exists mb :: mb in userBoxes && m in mb.messages)
    ensures isValid()
    ensures m.isRead
  {
    m.markAsRead();
  }
}

// Test
/* Can be used to test your code. */

method test() {
  var ma := new MailApp();
  assert ma.inbox.name == "Inbox";
  assert ma.drafts.name == "Drafts";
  assert ma.trash.name == "Trash";
  assert ma.sent.name == "Sent";
  assert ma.inbox.messages == ma.drafts.messages ==
         ma.trash.messages ==
         ma.sent.messages == {};

  ma.newMailbox("students");
  assert exists mb: Mailbox :: mb in ma.userBoxes &&
                               mb.name == "students" &&
                               mb.messages == {};

  var s := new Address("email@address.com");
  ma.newMessage(s);
  assert exists nw: Message :: ma.drafts.messages == {nw};
  
  // Test read/unread functionality
  var totalUnread := ma.totalUnreadMessages();
  assert totalUnread == 1; // The new message should be unread
  
  var message :| message in ma.drafts.messages;
  assert !message.isRead; // New message should be unread
  
  ma.readMessage(message);
  assert message.isRead; // Message should now be read
  
  totalUnread := ma.totalUnreadMessages();
  assert totalUnread == 0; // No unread messages
  
  message.markAsUnread();
  assert !message.isRead; // Message should be unread again
}