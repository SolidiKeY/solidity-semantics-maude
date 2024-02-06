contract AccountExample {
    struct Account {
        uint balance;
        bool isOpen;
    }

    struct Person {
        Account account;
        string name;
    }
}
