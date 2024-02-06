contract AccountExample {
    struct Account {
        uint balance;
        uint debt;
    }

    struct Person {
        Account account;
        uint age;
    }
}
