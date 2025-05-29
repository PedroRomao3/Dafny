/*===============================================
  M.EIC037: Formal Methods For Critical Systems

  Project 2 

  Your name(s): 
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
    modifies this
    ensures content == c
    ensures {id, date, sender} == old({id, date, sender})
    ensures recipients == old(recipients)
  {
    content := c;
  }

  method setDate(d: Date)
    modifies this
    ensures date == d
    ensures {id, sender} == old({id, sender})
    ensures recipients == old(recipients)
    ensures content == old(content)
  {
    date := d;
  }

  method addRecipient(p: nat, r: Address)
    modifies this
    requires p <= L.len(recipients) // allow adding at the end
    ensures L.len(recipients) == L.len(old(recipients)) + 1
    ensures L.elementSeq(recipients) == 
            L.elementSeq(L.take(old(recipients), p)) + [r] + L.elementSeq(L.drop(old(recipients), p))
    ensures {id, date, sender} == old({id, date, sender})
    ensures content == old(content)
  {
    recipients := InsertAt(recipients, p, r);
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

  constructor(n: string)
    requires n != "" // <- Enforced here
    ensures name == n
    ensures messages == {} // <- Empty on creation
  {
    name := n;
    messages := {};
  }

  method add(m: Message)
    modifies this
    ensures messages == old(messages) + {m}
    ensures name == old(name)
  {
    messages := { m } + messages;
  }

  method remove(m: Message)
    modifies this
    ensures messages == old(messages) - {m}
    ensures name == old(name)
  {
    messages := messages - { m };
  }

  method empty()
    modifies this
    ensures messages == {}
    ensures name == old(name)
  {
    messages := {};
  }
}



//==========================================================
//  MailApp
//==========================================================

ghost function ListElements<T>(l: L.List<T>): set<T>
{
  match l
    case Nil => {}
    case Cons(h, t) => {h} + ListElements(t)
}

lemma RemovePreservesExclusion<T(==)>(l: List<T>, x: T, y: T)
  ensures y !in elements(l) ==> y !in elements(remove(l, x))
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


class MailApp {
  ghost var userBoxes: set<Mailbox>

  ghost function systemBoxes(): set<Mailbox>
    reads this
  { {inbox, drafts, trash, sent} }

  var inbox: Mailbox
  var drafts: Mailbox
  var trash: Mailbox
  var sent: Mailbox

  var userboxList: List<Mailbox>

  ghost predicate isValid() reads this {
    inbox != drafts &&
    inbox != sent &&
    inbox != trash &&
    drafts != sent &&
    drafts != trash &&
    sent != trash &&
    inbox !in userBoxes &&
    drafts !in userBoxes &&
    trash !in userBoxes &&
    sent !in userBoxes &&
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

  method deleteMailbox(mb: Mailbox)
    modifies this, mb
    requires isValid()
    requires mb in userBoxes
    ensures isValid()
  {
    // Prove that system boxes stay out of the updated userBoxes
    RemovePreservesSystemBoxes(userboxList, mb, inbox, drafts, trash, sent);

    userboxList := remove(userboxList, mb);
    userBoxes    := ListElements(userboxList);
    mb.empty();
  }

  method newMailbox(n: string)
    modifies this
    requires isValid()
    requires n != ""
    requires forall mb: Mailbox :: mb in userBoxes ==> mb.name != n
    ensures isValid()
    ensures exists mb: Mailbox :: mb in userBoxes && mb.name == n && mb.messages == {}
    ensures fresh(userBoxes - old(userBoxes))
  {
    var mb := new Mailbox(n);
    userboxList := Cons(mb, userboxList);
    userBoxes := ListElements(userboxList);

    assert inbox !in userBoxes;
    assert drafts !in userBoxes;
    assert trash !in userBoxes;
    assert sent !in userBoxes;
  }

  method newMessage(s: Address)
    modifies this, drafts
    requires isValid()
    ensures isValid()
    ensures exists m: Message :: m in drafts.messages && m.sender == s && fresh(m)
    ensures |drafts.messages| == |old(drafts.messages)| + 1
    ensures forall m: Message :: m in old(drafts.messages) ==> m in drafts.messages
    ensures old(drafts.messages) == {} ==> (|drafts.messages| == 1 && 
            exists m: Message :: drafts.messages == {m} && m.sender == s && fresh(m))
  {
    var m := new Message(s);
    drafts.add(m);
  }

  method moveMessage(m: Message, mb1: Mailbox, mb2: Mailbox)
    modifies this, mb1, mb2
    requires isValid()
    ensures isValid()
  {
    mb1.remove(m);
    mb2.add(m);
  }

  method deleteMessage(m: Message, mb: Mailbox)
    modifies this, mb, trash
    requires isValid()
    requires mb != trash
    ensures isValid()
  {
    moveMessage(m, mb, trash);
  }

  method sendMessage(m: Message)
    modifies this, drafts, sent
    requires isValid()
    ensures isValid()
  {
    moveMessage(m, drafts, sent);
  }

  method emptyTrash ()
    modifies this, trash
    requires isValid()
    ensures isValid()
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

  ma.newMailbox("students");                              //THESE
  assert exists mb: Mailbox :: mb in ma.userBoxes &&      //LINES
                               mb.name == "students" &&   //YIELD
                               mb.messages == {};         //PROBLEMS

  var s := new Address("email@address.com");
  ma.newMessage(s);        
  assert exists nw: Message :: ma.drafts.messages == {nw};
}
