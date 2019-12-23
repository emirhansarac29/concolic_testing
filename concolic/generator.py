class Generator:
    def __init__(self):
        self.countstack = 0
        self.countdata = 0
        self.count = 0
        self.parameter = 0

    def gen_stack_var(self):
        self.countstack += 1
        return "s" + str(self.countstack)

    def gen_data_var(self):
        self.countdata += 1
        return "Id_" + str(self.countdata)

    def gen_data_var(self, position):
        return "Id_" + str(position)

    def gen_data_size(self):
        return "Id_size"

    def gen_mem_var(self, address):
        return "mem_" + str(address)

    def gen_mem_var(self, begin, bytecount):
        return "mem_" + str(begin) + "_" + str(bytecount)

    def gen_arbitrary_var(self):
        self.count += 1
        return "some_var_" + str(self.count)

    def gen_arbitrary_address_var(self):
        self.count += 1
        return "some_address_" + str(self.count)

    def gen_owner_store_var(self, position, var_name=""):
        return "storage_" + str(position)

    def gen_gas_var(self):
        self.count += 1
        return "gas_" + str(self.count)

    def gen_gas_price_var(self):
        return "Ip"

    def gen_address_var(self):
        return "Ia"

    def gen_caller_var(self):
        return "Is"

    def gen_origin_var(self):
        return "Io"

    def gen_balance_var(self):
        self.count += 1
        return "balance_" + str(self.count)

    def gen_balance_var(self, address):
        return "balance_" + str(address)

    def gen_code_var(self, address, position, bytecount):
        return "code_" + str(address) + "_" + str(position) + "_" + str(bytecount)

    def gen_code_size_var(self, address):
        return "code_size_" + str(address)

    def gen_par_var(self):
        self.parameter += 1
        return "parameter_" + str(self.parameter)