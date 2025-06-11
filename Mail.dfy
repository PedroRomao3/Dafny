/*===============================================
  M.EIC037: Formal Methods For Critical Systems

  Project 2 

  Your name(s):
  Pedro
  Bruno
  José 
  ===============================================*/

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

  // constructor creates a new message with sender s
  constructor(s: Address)
    ensures fresh(id) 
    ensures fresh(date)
    ensures content == ""
    ensures sender == s
    ensures recipients == L.Nil
  {
    id := new MessageId(0);  // placeholder
    date := new Date(0);     // placeholder
    content := "";
    sender := s;
    recipients := L.Nil;
  }

  method setContent(c: string)
    modifies this // modifies the content of the message
    ensures content == c // ensures the content is set to c
    ensures {id, date, sender} == old({id, date, sender}) // ensures the id, date and sender remain unchanged
    ensures recipients == old(recipients) // ensures the recipients remain unchanged
  {
    content := c;
  }

  method setDate(d: Date)
    modifies this // modifies the date of the message
    ensures date == d   // ensures the date is set to d
    ensures {id, sender} == old({id, sender}) // ensures the id and sender remain unchanged
    ensures recipients == old(recipients) // ensures the recipients remain unchanged
    ensures content == old(content) // ensures the content remains unchanged
  {
    date := d;
  }

  method addRecipient(position: nat, recipient: Address)
    modifies this // modifies the recipients of the message
    requires position <= L.len(recipients) // allow adding at the end
    ensures L.len(recipients) == L.len(old(recipients)) + 1 // ensures the number of recipients increases by 1
    ensures L.elementSeq(recipients) ==
            L.elementSeq(L.take(old(recipients), position)) + [recipient] + L.elementSeq(L.drop(old(recipients), position)) // ensures the new recipient is inserted at the correct position
    ensures {id, date, sender} == old({id, date, sender}) // ensures the id, date and sender remain unchanged
    ensures content == old(content) // ensures the content remains unchanged
  {
    recipients := InsertAt(recipients, position, recipient);
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
    modifies this // modifies the mailbox
    ensures messages == old(messages) + {m} // <- Adds m to the mailbox
    ensures name == old(name) // <- Name remains unchanged
  {
    messages := messages + {m};
  }

  // Removes message m from mailbox
  // m need not be in the mailbox
  method remove(m: Message)
    modifies this // modifies the mailbox
    ensures messages == old(messages) - {m} // <- Removes m from the mailbox
    ensures name == old(name) // <- Name remains unchanged
  {
    messages := messages - { m };
  }

  // Empties the mailbox
  method empty()
    modifies this // modifies the mailbox
    ensures messages == {} // <- Empty after emptying
    ensures name == old(name) // <- Name remains unchanged
  {
    messages := {};
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
    ensures sent.messages == {} // ensures all system mailboxes are empty
    ensures userBoxes == {} // ensures userboxList is empty
    ensures isValid() // ensures the state is valid after construction
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
    modifies this, mb // modifies the mailbox mb and the userBoxes
    requires isValid() // requires the state to be valid
    requires mb in userBoxes // requires mb is a user-defined mailbox
    ensures isValid() // ensures the state is still valid after deleting the mailbox
  {
    // Prove that system boxes stay out of the updated userBoxes
    RemovePreservesSystemBoxes(userboxList, mb, inbox, drafts, trash, sent);

    userboxList := remove(userboxList, mb);
    userBoxes    := ListElements(userboxList);
    mb.empty();
  }

  // Adds a new mailbox with name n to set of user-defined mailboxes
  // provided that no user-defined mailbox has name n already
  method newMailbox(n: string)
    modifies this // modifies the userBoxes and userboxList
    requires isValid() // requires the state to be valid
    requires n != "" // requires the name n is not empty
    requires forall mb: Mailbox :: mb in userBoxes ==> mb.name != n // requires no mailbox with name n already exists
    ensures isValid() // ensures the state is still valid after adding the mailbox
    ensures exists mb: Mailbox :: mb in userBoxes && mb.name == n && mb.messages == {} // ensures a new mailbox with name n is added
    ensures [inbox, drafts, trash, sent] == old([inbox, drafts, trash, sent]) // ensures the system mailboxes remain unchanged
    ensures fresh(userBoxes - old(userBoxes)) // ensures the new mailbox is fresh
  {
    var mb := new Mailbox(n);
    userboxList := Cons(mb, userboxList);
    userBoxes := ListElements(userboxList);
  }

  // Adds a new message with sender s to the drafts mailbox
  method newMessage(s: Address)
    modifies this, drafts // modifies the drafts mailbox
    requires isValid() // requires the state to be valid
    ensures isValid() // ensures the state is still valid after adding the message
    ensures exists m: Message :: m in drafts.messages && m.sender == s && fresh(m) // ensures a new message is added to the drafts mailbox
    ensures |drafts.messages| == |old(drafts.messages)| + 1 // ensures the number of messages in drafts increases by 1
    ensures forall m: Message :: m in old(drafts.messages) ==> m in drafts.messages // ensures all old messages remain in the drafts mailbox
    ensures old(drafts.messages) == {} ==> (exists m: Message :: drafts.messages == {m}) // ensures if drafts was empty, it now contains the new message
  {
    var m := new Message(s);
    drafts.add(m);
  }

  // Moves message m from mailbox mb1 to a different mailbox mb2
  method moveMessage(m: Message, fromMailbox: Mailbox, toMailbox: Mailbox)
    modifies this, fromMailbox, toMailbox // modifies the message m and the origin and destination mailboxes
    requires isValid() // requires the state to be valid
    requires fromMailbox != toMailbox // requires the origin and destination mailboxes to be different
    ensures isValid() // ensures the state is still valid after moving the message
    ensures m !in fromMailbox.messages // ensures m is not in the origin mailbox after moving
    ensures m in toMailbox.messages // ensures m is in the destination mailbox after moving
    ensures fromMailbox.messages == old(fromMailbox.messages) - {m} // ensures m is removed from the origin mailbox
    ensures toMailbox.messages == old(toMailbox.messages) + {m} // ensures m is added to the destination mailbox
  {
    fromMailbox.remove(m);
    toMailbox.add(m);
  }

  // Moves message m from non-null mailbox mb to the trash mailbox
  // provided that mb is not the trash mailbox
  method deleteMessage(m: Message, mb: Mailbox)
    modifies this, mb, trash // modifies the mailbox mb and the trash mailbox
    requires isValid() // requires the state to be valid
    requires mb != trash // requires the mailbox mb to be different from the trash mailbox
    ensures isValid() // ensures the state is still valid after moving the message
  {
    moveMessage(m, mb, trash);
  }

  // Moves message m from the drafts mailbox to the sent mailbox
  method sendMessage(m: Message)
    modifies this, drafts, sent // modifies the drafts mailbox, message m and the sent mailbox
    requires isValid() // requires the state to be valid
    ensures isValid() // ensures the state is still valid after sending the message
  {
    moveMessage(m, drafts, sent);
  }

  // Empties the trash mailbox
  method emptyTrash ()
    modifies this, trash // modifies the trash mailbox
    requires isValid() // requires the state to be valid
    ensures isValid() // ensures the state is still valid after emptying the trash
  {
    trash.empty();
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
  //assert ma.drafts.messages == {};
  assert exists mb: Mailbox :: mb in ma.userBoxes &&
                               mb.name == "students" &&
                               mb.messages == {};

  var s := new Address("email@address.com");
  ma.newMessage(s);
  assert exists nw: Message :: ma.drafts.messages == {nw};
}