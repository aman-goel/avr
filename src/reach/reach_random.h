/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
*
************************************************************************************/

#pragma once

#include <random>
#include <algorithm>

namespace avr_rand {
    inline std::mt19937& get_random_engine() {
        thread_local static std::random_device rd;
        thread_local static std::mt19937 gen(rd());
        return gen;
    }

    template<typename Container>
    void shuffle(Container& container) {
        std::shuffle(container.begin(), container.end(), get_random_engine());
    }

    template<typename Iterator>
    void shuffle(Iterator begin, Iterator end) {
        std::shuffle(begin, end, get_random_engine());
    }
}
