#!/usr/bin/env python3

if __name__ == '__main__':
    my_list = [5, 4, 3, 8, 1]
    changed = True
    my_list_len = len(my_list)  # cache the length
    while changed:
        changed = False
        if my_list_len > 0:
            prev = my_list[0]       # save the first element to use in the loop
        for i in range(1, my_list_len):
            current = my_list[i]
            if prev <= current:
                # save for the next iteration
                prev = current
            else:
                # swap the elements
                my_list[i - 1] = current
                my_list[i] = prev
                changed = True

    print(my_list)                

