#ifndef GUEST_INFORM_H
#define GUEST_INFORM_H

#include "vosys-internal.h"

void guest_inform_init(void);
void guest_inform_connect(void);

void guest_inform_checkpoint_started(void);
void guest_inform_checkpoint_finished(void);

void guest_inform_reload(void);

#endif /* GUEST_INFORM_H */
